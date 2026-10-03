# Two disjoint core edges and arbitrary balanced cores

Status: independently approved on October 1, 2026, including all seven arbitrary-class Rayleigh identities and the arbitrary-subset-of-K2,2 consequence. This approval supersedes the conditional review language below. No priority claim.

## Directed two-edge theorem

Let P={p1,p2}, Q={q1,q2}, and I be independent. Include core arcs p1→q1 and p2→q2, and arbitrary exterior arcs P→I and I→Q, but no other arcs. For arbitrary nonnegative independent tail/head activities, the signed physical monomer polynomial is real stable. Consequently gamma has only negative real roots and is rank-ULC at its actual surviving degree. Transitivity is unnecessary.

Use the same split copies, rank-two side matroids, basis polynomials B_P,B_Q, element sums L_P,L_Q, and exterior monomer product Z as in the approved complete-core and one-missing-edge notes. Let r_Pi be the class containing dummy pi and copies private to pi; define r_Qj analogously. The correct split kernel is

    H = B_P B_Q − L_P L_Q + 1 + r_P1 r_Q2 + r_P2 r_Q1.

To see this, begin with the complete-core support kernel. The two omitted off-diagonal edges remove exactly the one-core-edge supports whose residual source and sink are uniquely forced to those endpoints. These two lost sets are disjoint. A common-neighbor exterior copy never forces one residual core endpoint and so is absent from the corrections. The two-core-edge support survives through the diagonal perfect matching and contributes1 once. This is a support decomposition, not edgewise counting of matching witnesses.

## Abstract kernel and all-real Rayleigh identities

Write P-side parallel-class sums as p0,p1,p2,... and Q-side class sums as q0,q1,q2,.... For this argument label q0=r_Q2 and q1=r_Q1, so the two correction terms are partnered: p0q0+p1q1. Put

    P=e2(p), Q=e2(q), L=sum(p), M=sum(q),
    K=p0q0+p1q1, H=P Q−L M+1+K.

The first two classes on each side are distinguished; other classes are ordinary. This polynomial is multiaffine in the independent class variables. By the all-real multiaffine Rayleigh criterion, it is enough to show Δ_xy=(∂xH)(∂yH)−H∂x∂yH≥0 for every variable pair and every real assignment. The following seven cases are exhaustive under side interchange, simultaneous exchange of the partnered labels0,1, and permutations of ordinary classes. All sums of squares below omit precisely the listed indices; empty sums are zero.

Every identity follows algebraically from e2(z)=((sum z)^2−sum z^2)/2, so the number of ordinary classes is unrestricted.

### 1. Same side, both distinguished: x=p0, y=p1

Set A=sum_{k≥2}p_k, U=sum_{k≥2}p_k², B=sum_{l≥2}q_l, V=sum_{l≥2}q_l². Then

    2Δ = (Q A−B)² + Q²U + V.

### 2. Same side, one distinguished: x=p0, y=pi, i≥2

Set A=sum_{k≠0,i}p_k, U=sum_{k≥2,k≠i}p_k², V=sum_{l≥2}q_l². Then

    2Δ = [Q A−(M−q0)]² + (Q p1−q1)² + Q²U + V.

### 3. Same side, both ordinary: x=pi, y=pj, i,j≥2

Set A=sum_{k≠i,j}p_k, U=sum_{k≥2,k≠i,j}p_k², V=sum_{l≥2}q_l². Then

    2Δ = (Q A−M)² + (Q p0−q0)² + (Q p1−q1)² + Q²U + V.

### 4. Opposite sides, partnered distinguished: x=p0, y=q0

Set A=sum_{k≠0}p_k, U=sum_{k≥2}p_k², B=sum_{l≠0}q_l, V=sum_{l≥2}q_l². Then

    2Δ = (A q1−B p1)² + A²V + B²U.

### 5. Opposite sides, unpartnered distinguished: x=p0, y=q1

Set u=p1, v=q0, A=sum_{k≠0}p_k, U=sum_{k≥2}p_k², B=sum_{l≠1}q_l, V=sum_{l≥2}q_l². Then

    4Δ = (A B+u B+v A−u v−2)²
          + U(B−v)² + V(A−u)² + U V.

### 6. Opposite sides, one distinguished: x=p0, y=qj, j≥2

Set r=p1, s=q1, v=q0, A=sum_{k≠0}p_k, U=sum_{k≥2}p_k², B=sum_{l≠j}q_l, V=sum_{l≥2,l≠j}q_l². Then

    4Δ = [A(B+v)−r s−2]² + [A s−r(B−v)]²
          + V(A²+r²) + U[(B−v)²+s²] + U V.

### 7. Opposite sides, both ordinary: x=pi, y=qj, i,j≥2

Set A=sum_{k≠i}p_k, U=sum_{k≥2,k≠i}p_k², B=sum_{l≠j}q_l, V=sum_{l≥2,l≠j}q_l², R2=p0²+p1², S2=q0²+q1². Then

    4Δ = (A B−K−2)² + (A q0−B p0)² + (A q1−B p1)²
          + (p0q1−p1q0)² + U(B²+S2) + V(A²+R2) + U V.

Each expression is a sum of squares after expanding U,V. Thus all Rayleigh differences are nonnegative everywhere on real space. H is nonzero because its constant coefficient is1. The criterion proves real stability. Substituting each nonempty parallel-class sum then proves stability in individual side-matroid variables, including multiple variables in a class.

## Physical monomers and weighted conclusion

Give core dummies their monomer variables and replace active exterior-copy variables by −1/z. Multiply by Z; multiaffinity cancels denominators and yields the exact split signed monomer polynomial by the support kernel above. Negative reciprocal substitution preserves the upper half-plane. Introduce positive role activities by (∏w_i)μ(z_i/w_i). Merge each physical pair using ab↦z, a↦1, b↦1, 1↦0; its symbol z+u+v is stable. This removes double use without matching multiplicities. The empty-support monomial has coefficient1. Zero activities follow by continuity. Finally μ(t,...,t)=t^N Γ(−t^(−2)) implies negative real roots of gamma, and Newton applies at its actual degree. These are the already approved operations of ../BALANCED_REAL_ROOTEDNESS_PROOF.md.

## Consequence: every balanced core subset

The preceding theorem, together with the approved complete-core, one-missing-edge and two-edge-star results, covers core patterns with4,3,2 edges. The two-edge cases are either adjacent (the star or its reversal) or disjoint (this theorem).

The empty core has stable split kernel B_P B_Q. For a single edge pi→qj the split kernel is

    B_P B_Q − (∂_{d_pi}B_P)(∂_{d_qj}B_Q)
      = (1−∂_{d_pi}∂_{d_qj})(B_P B_Q).

On polynomials affine in the two dummy variables a,b, the differential operator1−∂a∂b has symbol (a+x)(b+y)−1. It is stable: a+x and b+y are upper-half-plane numbers, whose product cannot equal the positive real number1. Full symbols add only stable factors for untouched variables. The constant all-dummy coefficient survives, so the output is nonzero. The same physical and activity transformations apply.

Therefore, if this note passes independent review, arbitrary subsets J⊆P×Q of the four core arcs give real-stable weighted physical monomer polynomials and actual-degree real-rooted gamma. No transitivity is needed. This includes all exterior attachment populations, not only preorder-legal ones.

## Sources and checks

- All-real Rayleigh criterion: Wagner survey Theorem3.1, citing Brändén Theorem5.6; https://www.math.uwaterloo.ca/~dgwagner/ceb_wagner.pdf .
- Finite-degree symbol criterion: Borcea–Brändén PartI, Theorem1.1; https://arxiv.org/abs/0809.0401 .
- verify_matching_squares.py verifies the seven identities exactly with four class variables on each side; the aggregate identities above prove arbitrary class count.
- The two-edge star and three-edge notes and their independent receipts are in this directory. Their frozen proofs are unchanged by this note.
