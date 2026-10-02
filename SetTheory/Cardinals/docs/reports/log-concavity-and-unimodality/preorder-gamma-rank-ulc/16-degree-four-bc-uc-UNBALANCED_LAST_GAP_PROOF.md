# Last Newton inequality for every outward 1+3 core star

Status: independently audited and approved (2026-10-01), including every core-neighborhood subset J, the polarization normalization, Q-loops, zero cases, the Rayleigh specialization and the final square. Exact seven-type certificates were independently reconstructed as additional verification.

## Statement and support convention

Let p be a source core vertex, Q={q1,q2,q3} three sink core vertices, with an arbitrary subset J⊆Q of the arcs p→q_i and no other internal core arcs. Exterior vertices are pairwise nonadjacent, each with any nonempty subset of the four core vertices as neighbors. Arcs run p→x and/or x→Q. All vertex activities are one, and gamma counts ordered DISJOINT tail/head supports admitting a directed matching, once per support.

Then

3 Gamma₃²≥8 Gamma₂ Gamma₄.

No real-rootedness of Gamma is asserted; that stronger property fails in this family.

## 1. A one-source decomposition

Let Q(t)=1+L t+B t²+T t³ be the matching-support polynomial of the three-sink side alone, using all exterior vertices and only their arcs to Q. An exterior vertex having no Q-neighbor is a loop for this side and contributes nothing.

Let H be the set of exterior vertices adjacent to p and m=|H|. For each x∈H, let Q_{−x}(t) be this three-sink polynomial after deleting x. Define

R(t)=Σ_{x∈H}Q_{−x}(t)=m+A t+C t²+D t³.

Let Q⁺(t)=1+L⁺t+B⁺t²+T⁺t³ be the three-sink polynomial after adjoining one new exterior vertex with neighborhood J. If J is empty, the new vertex is a loop and Q⁺=Q. Then

Gamma(t)=Q⁺(t)+tR(t).                       (1)

Indeed, supports with no exterior head are exactly the supports of the Q-side with p allowed as the added tail of neighborhood J. Otherwise the unique exterior head x must be matched from p, and the remaining support is a Q-side support omitting x. Different choices of x give distinct head supports, so the sum introduces no matching multiplicity. The deletion prevents a physical vertex from simultaneously being an exterior head and an exterior tail.

For reference, in the full-star case J=Q, if n is the number of Q-active exterior vertices, Ai counts the vertices with singleton neighborhood {qi}, and Z counts the vertices with at least two Q-neighbors, then

L⁺=L+3,
B⁺=B+E1,  E1=2n+Z,
T⁺=T+E2,  E2=binomial(n,2)−Σ_i binomial(Ai,2).

These identities count supports containing the newly adjoined universal vertex in that full-star case. They are not needed separately in the final square argument.

## 2. Deletion averages satisfy the degree-three last inequality

The exact homogeneous degree-three polynomial

R_h(z,t)=m z³+A z²t+C zt²+D t³

is Lorentzian. Therefore

C²≥3AD.                                    (2)

Here is a construction proving the claim without dividing any polynomial by a monomial.

Add one private dummy element for each sink q_i and form the rank-three transversal matroid on the exterior vertices and these dummies. A basis is a feasible exterior support together with the private dummies for the unselected sink vertices. Its basis polynomial counts each exterior/sink support once. The basis polynomial is Lorentzian by the matroid theorem.

Identify all dummy variables with z, the m variables indexed by H with s, and all remaining exterior variables with t. Denote the resulting degree-three Lorentzian polynomial by q(z,s,t). Variables for Q-loops in H may be formally included even though the polynomial does not depend on them; the degree bound in s is still m.

Polarize s into m slots using the degree bound m. This sends s^k to e_k(s1,...,sm)/binomial(m,k) and preserves the Lorentzian property. Set s1=0 and s2=...=sm=t. Each original monomial involving k vertices of H is multiplied by

binomial(m−1,k)/binomial(m,k)=(m−k)/m.

Multiplying the result by m gives exactly R_h, because that Q-support survives deletion of m−k eligible vertices. Nonnegative linear substitutions and zero specialization preserve Lorentzianity. If m=0, R=0 and the theorem is already immediate.

This proves only the displayed bivariate R_h claim. The stronger statement with all original exterior variables kept separately is false and is not used.

The relevant primary reference is Brändén–Huh, *Lorentzian polynomials*, Proposition3.1 for polarization and Theorem2.10 for nonnegative substitutions, together with their matroid characterization. Verified author PDF: https://web.math.princeton.edu/~huh/Lorentzian.pdf .

## 3. Three-center pair/triple ratio is monotone

For any ordinary population on three centers, let B and T be its two-edge and three-edge matching-support counts. If one additional exterior vertex e of any neighborhood is added, then

T_new B−T B_new≥0.                         (3)

For the empty neighborhood the polynomial is unchanged. For every other neighborhood this follows directly from Wagner's theorem that every rank-three matroid is Rayleigh.

Form the rank-three transversal matroid on the old exterior vertices, the new element e, and the three private dummy elements d1,d2,d3. Write its basis polynomial as f. The Rayleigh inequalities, in derivative notation, say

(∂e f)(∂di f)−f(∂e∂di f)≥0

at nonnegative variable values, where zero boundary values follow by continuity from strictly positive values. Set each old exterior variable to1 and set e=d1=d2=d3=0. At this point,

f=T,
∂e f=DeltaT:=T_new−T,
Σ_i ∂di f=B,
Σ_i ∂e∂di f=DeltaB:=B_new−B.

The identities count bases with no dummy, one dummy, or the indicated distinguished elements. In particular a two-edge support has exactly one complementary private dummy, so it contributes once to the indicated sum. Summing the three Rayleigh inequalities gives

DeltaT·B−T·DeltaB≥0,

which is exactly (3). This proof also allows arbitrary nonnegative weights on the old exterior elements.

Primary source: David G. Wagner, *Rank–Three Matroids are Rayleigh*, The Electronic Journal of Combinatorics12(2005),#N8, Theorem1.1. The theorem and Rayleigh definition were verified in the author's arXiv manuscript, https://arxiv.org/pdf/math/0403216 , pages1–2; published record: https://www.combinatorics.org/ojs/index.php/eljc/article/view/v12i1n8 .

### Independent exact verification

The ordinary-population instance of (3) also has a standalone rational certificate in the seven neighborhood populations. The checker /workspace/shared/three-center-gap/prove_weaker.py constructs B,T by Boolean feasibility, then reconstructs every addition numerator as a nonnegative falling-factorial sum, plus at most one half-square. Its certificate is approved_candidate_certificates.json and receipt verification_receipt.json in the same directory. Types1,2,4 each have147 positive terms; types3,5,6 each have223 positive terms plus a half-square; type7 has266 positive terms. These are supplementary verification and are not required by the analytic proof above.

## 4. Compatibility with the core-neighborhood extension

Assume D>0. Then T>0 and B>0: a degree-three Q-support exists, hence so do degree-two Q-supports. The same holds for B⁺ and T⁺. Also C>0.

For each x∈H, denote the coefficients of Q_{−x} by B_x,T_x. Adding x back (or doing nothing if x is a Q-loop), and then adding the vertex of neighborhood J, gives by (3)

T_x B≤B_x T,
T B⁺≤B T⁺.

Multiply and cancel the positive B to obtain T_x B⁺≤B_x T⁺. This does not divide by B_x, which may be zero; if B_x=0 then T_x=0 by heredity anyway. Summing over x yields

D B⁺≤C T⁺.                                (4)

All zero cases are now covered: if D=0 the desired final inequality is immediate. If D>0 the quantities divided or canceled above are strictly positive. Eligible Q-loops are handled by equality in the first addition step and by their formal polarization slots in section2.

## 5. The final square

By (1), Gamma₂=A+B⁺, Gamma₃=C+T⁺, and Gamma₄=D. Combining (2) and (4),

3 Gamma₃²−8 Gamma₂ Gamma₄
=3(C+T⁺)²−8(A+B⁺)D
≥ C²/3−2C T⁺+3(T⁺)²
=(C−3T⁺)²/3
≥0.

The argument uses no transitivity assumption. It applies to every directed graph of the stated independent-exterior, outward-star form, and also to its reversal. Within the retained canonical a4 templates it covers IDs1,4,10 (respectively one, two, or three core arcs); the zero-core case is already bipartite. The exact map is saved as applicable_star_templates.json beside this proof.

This completes the proof. The stated constructions and applications of the cited theorems have been independently audited.
