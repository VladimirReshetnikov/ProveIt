# Structural proof of the last degree-four Newton inequality

Status: independently audited and approved (2026-10-01). The audit checked every mathematical step, reproduced the supplied scripts, and independently exhausted 3,876 labeled-type multisets with at most four exterior vertices; all 275 distinct core-deleted polynomials were checked by exact root isolation. Audit receipt: independent-audit/balanced_last_gap_audit_receipt.json beside this note. This is a proof of ultra-log-concavity at the last index, not a proof of real-rootedness of the full gamma polynomial.

## The family and the exact decomposition

There are two source core vertices P={p1,p2}, two sink core vertices Q={q1,q2}, and all four arcs P→Q. Exterior vertices are pairwise nonadjacent. Each exterior vertex x has arbitrary neighbor subsets P(x)⊆P and Q(x)⊆Q, not both empty, with arcs P(x)→x→Q(x). All activities are one.

Gamma counts ordered DISJOINT tail/head supports admitting a directed matching, once per support and not once per matching. Let

- m = number of exterior vertices with P(x) nonempty
- n = number of exterior vertices with Q(x) nonempty
- r = number having both
- u = 2(m+n), v = mn−r

Delete the four core arcs, and denote the resulting support polynomial by

F(t)=1+a t+b t²+c t³+d t⁴.

Then the original polynomial is exactly

Gamma(t)=F(t)+4t+(u+1)t²+v t³.                 (1)

Indeed, if a support uses h exterior heads, j exterior tails, A⊆P and B⊆Q, its number of core edges in every matching is s=|A|−h=|B|−j. For s=0 it is counted by F. For s=1, the four possible (|A|,|B|) shapes give respectively 4, 2m, 2n, and v supports at degrees 1,2,2,3. The degree-three count is the number of an eligible exterior head and eligible exterior tail that are distinct, namely mn−r. For s=2, only the support with all four core vertices occurs, contributing t² exactly once. Completeness of P→Q makes the separate exterior injections sufficient for feasibility.

## Lemma 1: F is real-rooted

For the source side, assign one variable z_x per physical exterior vertex. Let A and B be the vertices adjacent only to p1 or only to p2; let Z be the vertices adjacent to both. Vertices adjacent to neither do not enter this side polynomial. Define

f_P(z)=e₂(1+Σ_{x∈A}z_x, 1+Σ_{x∈B}z_x, (z_x)_{x∈Z}).

The two constant ones can be viewed as two distinct dummy elements in the two private parallel classes. Expanding gives constant coefficient 1, singleton coefficient |P(x)|, and pair coefficient 1 exactly when the two vertices admit a matching to the two P centers. Thus each feasible pair is counted once. Define f_Q analogously.

The elementary symmetric polynomial e₂ is real stable. One elementary proof differentiates the stable polynomial ∏_i(s+y_i) the required number of times in s, and specializes s=0. Real stability is preserved by differentiation, nonnegative affine substitutions, and real specialization (unless the result is zero). Consequently f_P and f_Q are stable.

Let MA remove every monomial that has exponent ≥2 in any physical exterior variable. Then

F(t)=MA(f_P(z)f_Q(z))|_{z_x=t for all x}.     (2)

The product enumerates choices of exterior heads and tails, including possible overlaps. MA removes exactly those choices using the same physical exterior vertex in both roles. It does not alter any surviving coefficient.

For completeness, MA preserves stability. Apply degree-at-most-one truncation one variable at a time. Fix all other variables in the open upper half-plane, and write the remaining univariate polynomial as h(z). Its roots ρ_i are outside the open upper half-plane. If h(0)≠0, then the root of h(0)+z h′(0), when nonconstant, is

−h(0)/h′(0)=1/(Σ_i 1/ρ_i),

which lies in the closed lower half-plane because each 1/ρ_i has nonnegative imaginary part. If the specialization h(0) vanishes at an upper-half-plane point in the other variables, the multivariate boundary-specialization theorem (Hurwitz) says its coefficient polynomial is identically zero. Factor out z, and apply the same boundary-specialization statement to the remaining factor to handle the linear coefficient; the truncation is then either stable or identically zero. This proves the one-variable operation preserves stability. Iterating proves the assertion. In our case the constant term is 1, so the result is not zero.

Alternatively, the finite-degree Borcea–Brändén symbol for the one-variable truncation on degree ≤2 is w²+2zw=w(w+2z), which is stable; the multivariable symbol is the product of these factors.

Diagonal specialization in (2) is stable and real, hence real-rooted. Since its coefficients are nonnegative and its constant term is 1, all nonconstant roots are strictly negative. If d>0, Newton's degree-four inequality therefore gives

3c² ≥ 8bd.                                 (3)

## Lemma 2: two elementary counting bounds

Assume d>0, so m,n≥2 and m+n−r≥4.

First,

v² ≥ 4d.                                   (4)

Each degree-four support of F consists of a feasible pair H of exterior heads and a disjoint feasible pair T of exterior tails. There are exactly four ordered decompositions of this support into two eligible ordered head/tail pairs. All are counted in v², and different supports yield disjoint decompositions.

Second,

c ≥ (10/3)(1/m+1/n)d.                       (5)

For any population of exterior vertices available to one two-center side, let A,B,Z be the private/private/common population sizes. The singleton and pair support counts and active population are

p₁=A+B+2Z,
p₂=AB+(A+B)Z+Z(Z−1)/2,
N=A+B+Z.

The exact identity

6N p₁−20p₂=(A+B−Z)²+Z²+5(A−B)²+10Z ≥0

proves p₂≤(3/10)N p₁. Fix a feasible Q-tail pair T. The remaining P-eligible population has N≤m, so the number of feasible P-head pairs disjoint from T is at most (3/10)m times the weighted count of P-head singletons disjoint from T. Summing over T shows d≤(3/10)m c_{1,2}, where c_{1,2} is the part of c with one exterior head and two exterior tails. The symmetric inequality is d≤(3/10)n c_{2,1}. Since c=c_{1,2}+c_{2,1}, (5) follows.

## The last Newton gap

From (1), the required expression is

3 Gamma₃²−8 Gamma₂ Gamma₄
=(3c²−8bd)+E,
E=6cv+3v²−8(u+1)d.                         (6)

The first parenthesis is nonnegative by (3). It remains to prove E≥0.

### Case max(m,n)≥5

Let M=max(m,n). Since r≤min(m,n), (5) implies

cv ≥ (10/3)d(m+n)(1−r/(mn))
   ≥ (10/3)d(m+n)(1−1/M)
   ≥ (8/3)d(m+n).

Thus 6cv≥8ud. Applying (4) in (6) gives E≥3v²−8d≥4d≥0.

### Case 2≤m≤n≤4

Set

K=20v(m+n)/(mn)−16(m+n)−8.

By (5), E≥3v²+Kd. If K≥−12, (4) immediately gives E≥0. The only remaining possibilities are three very small cases, as follows.

For fixed (m,n), K decreases with r, and d>0 requires r≤min(m,m+n−4). At the largest allowed r, the six possibilities are:

| m | n | largest r | smallest K |
|---|---|-----------|------------|
| 2 | 2 | 0 | 8 |
| 2 | 3 | 1 | −14/3 |
| 2 | 4 | 2 | −14 |
| 3 | 3 | 2 | −32/3 |
| 3 | 4 | 3 | −15 |
| 4 | 4 | 4 | −16 |

For the three rows with K<−12, decreasing r by one raises K above −12. Thus the only outstanding triples are (m,n,r)=(2,4,2),(3,4,3),(4,4,4). Each has exactly four active exterior vertices. Once the P-head pair is chosen, the Q-tail pair is its uniquely determined complement, so d≤binomial(m,2). Direct substitution gives:

| (m,n,r) | v | K | upper bound on d | lower bound on E |
|---------|---|---|------------------|------------------|
| (2,4,2) | 6 | −14 | 1 | 108−14=94 |
| (3,4,3) | 9 | −15 | 3 | 243−45=198 |
| (4,4,4) | 12 | −16 | 6 | 432−96=336 |

This proves E≥0 in every case. If d=0, the desired inequality is immediate. Therefore every graph in this full balanced 2+2 core family satisfies

3 Gamma₃² ≥ 8 Gamma₂ Gamma₄.

## Scope and source notes

The proof is for unit vertex populations and arbitrary multiplicities of all 15 nonempty exterior neighbor types. It allows a physical exterior vertex to have both roles, but never simultaneously in a support. The polynomial F, obtained by deleting core edges, is proved real-rooted. Real-rootedness of Gamma itself is not established here.

Standard stability closure facts can be sourced to Borcea and Brändén, *Multivariate Pólya–Schur classification problems in the Weyl algebra*, https://arxiv.org/abs/math/0606360, and to David Wagner's author-hosted survey, https://www.math.uwaterloo.ca/~dgwagner/ceb_wagner.pdf. The proof above supplies the specific truncation argument rather than relying solely on an operator citation.
