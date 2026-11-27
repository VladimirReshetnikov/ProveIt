# Literature comparison and priority limits

Review date: November 26, 2026 (Pacific). This is a focused comparison of the exact compression formula and its consequences, not an exhaustive historical survey.

## What the accompanying paper contributes

For fixed injective frames with alternating Gram matrices \(F\) and \(H\) in a finite symplectic space, the paper determines the probability of each cross-Gram matrix \(M\). It counts possible kernels of the concatenated frame inside

\[
\operatorname{rad}\begin{pmatrix}F&M\\-M^{\mathsf T}&H\end{pmatrix},
\]

with the requirement that the kernel meet neither coordinate summand. This gives an explicit law for arbitrary, possibly degenerate, row and column forms and a simple exact support criterion. It also gives a computable first correction to uniformity and the sharp fixed-dimension total-variation scale \(q^{-2N}\), where the ambient space has dimension \(2N\).

The further balanced rectangular result concerns two nonsingular restricted forms. It identifies an optimal test based on the induced form, proves a positive limiting full-distribution discrepancy \(\Delta_q\), and shows that the total-variation distance of the rank distributions tends to zero. The supplied Article already proves rank blindness for a **Lagrangian target** and nonsingular source. The new result extends that analysis to the stated regime with **both forms nonsingular**; it is not a claim to have discovered the general phenomenon of rank blindness.

The classification of alternating forms, Witt extension, fixed-Gram embedding counts, and ordinary Gaussian subspace counts are classical ingredients. Their use here is not presented as a new discovery. The main contribution is the assembled cross-Gram law with the two separate injectivity constraints, its support criterion, and the stated asymptotic consequences.

## The supplied Article: the direct starting point

At commit `fc9889c80312959aee9893ab21bfc9e741719e88`, [sections/spn.tex](https://github.com/VladimirReshetnikov/ProveIt/blob/fc9889c80312959aee9893ab21bfc9e741719e88/Analysis/GeneralizedRiemannHypothesis/Article/sections/spn.tex) contains the following closely related statements:

| Article label | Scope relevant to this paper |
|---|---|
| `spn:thm:symplectic-exact` | Exact limiting discrepancy for an isotropic compression family. |
| `spn:thm:lagrangian` | Likelihood of every matrix for a Lagrangian projection and arbitrary source form. |
| `spn:thm:rank-blind` | A persistent full-distribution obstruction invisible asymptotically to rank tests, for a Lagrangian target and nonsingular source. |
| `spn:q:symplectic` | Asks for the law or limiting discrepancy for two arbitrary compressed subspaces, without requiring either to be Lagrangian. |

The accompanying general formula answers this last question. This is a precise extension relative to the supplied text; it does not, by itself, establish priority over the entire finite-geometry literature.

## Earlier form-representation and subspace counts

### Wan (1995)

Zhe-Xian Wan, *Representations of Forms by Forms in a Finite Field*, **Finite Fields and Their Applications 1**(3), 297–325. [DOI: 10.1006/ffta.1995.1024](https://doi.org/10.1006/ffta.1995.1024).

The [publisher abstract](https://www.sciencedirect.com/science/article/pii/S1071579785710246) covers representation counts for alternating bilinear forms over finite fields of both odd and even characteristic. This is direct prior art for fixed-Gram counts. Only the abstract was available for this review; the full article was not inspected. Consequently this review cannot exclude a formula in that paper from implying the present blockwise-injective enumeration after further manipulation.

### Wei and Zhang (2001)

Hongzeng Wei and Yibin Zhang, *The number of solutions to the alternate matrix equation over a finite field and a q-identity*, **Journal of Statistical Planning and Inference 94**(2), 349–358. [DOI: 10.1016/S0378-3758(00)00265-2](https://doi.org/10.1016/S0378-3758(00)00265-2).

The [publisher abstract and introductory material](https://www.sciencedirect.com/science/article/abs/pii/S0378375800002652) describe counts of prescribed-rank matrices satisfying \(XAX^{\mathsf T}=B\), for alternating \(A,B\), in all characteristics. Thus Gram constraints with a total-rank condition are established prior art. Requiring two column blocks to be separately injective is a different restriction, but the unavailable full text prevents a definitive exclusion of overlap. The introduction also records earlier work by Carlitz, Hodges, and Buckhiester; those earlier papers were not independently inspected for this review.

### Guo, Li, and Wang (2013)

Jun Guo, Fenggao Li, and Kaishun Wang, *Anzahl formulas of subspaces in symplectic spaces and their applications*, **Linear Algebra and its Applications 438**(8), 3321–3335. [DOI: 10.1016/j.laa.2012.12.008](https://doi.org/10.1016/j.laa.2012.12.008).

The [publisher abstract](https://www.sciencedirect.com/science/article/pii/S0024379512008476) reports counts for families of symplectic subspaces with applications to codes, designs, and semilattices. The abstract does not specify enough invariants to decide exact overlap with the arbitrary cross-Gram law. It is a necessary comparator, not evidence either establishing or disproving priority of the complete formula.

### Gruica and Ravagnani (2022)

Anina Gruica and Alberto Ravagnani, *Common Complements of Linear Subspaces and the Sparseness of MRD Codes*, **SIAM Journal on Applied Algebra and Geometry 6**(2), 79–110. [DOI: 10.1137/21M1428947](https://doi.org/10.1137/21M1428947).

The relevant part of Section 2 of the [university-hosted published paper](https://pure.tue.nl/ws/portalfiles/portal/240233203/21m1428947.pdf) was inspected. It treats counts involving fixed subspaces and common complements. This is related to the elementary count of kernels disjoint from two coordinate summands. The kernel-count lemma in the accompanying paper is presented as a counting ingredient, without a separate historical novelty claim.

### De Boeck and Van de Voorde (2024)

Maarten De Boeck and Geertrui Van de Voorde, *Anzahl theorems for trivially intersecting subspaces generating a non-singular subspace I: symplectic and hermitian forms*, **Linear Algebra and its Applications 699**, 367–402. [DOI: 10.1016/j.laa.2024.07.004](https://doi.org/10.1016/j.laa.2024.07.004); [arXiv:2407.07486v3](https://arxiv.org/html/2407.07486v3).

The introduction and relevant symplectic results, especially Theorems 4.7–4.9, were inspected. They fix a subspace of arbitrary type and count nonsingular subspaces disjoint from it whose sum with it is nonsingular. Those are exact aggregate counts. The stated main result is narrower than a pointwise law for every cross-Gram matrix with unrestricted degeneracy on both sides and in the total span. This scope distinction does not assert that their techniques cannot imply further refinements.

## Recent comparisons

### Ishizuka (2026)

Keita Ishizuka, *Uniform Sampling of Linear Codes with Prescribed Hull Dimension*, [arXiv:2611.03578v2](https://arxiv.org/html/2611.03578v2).

Sections 2.3 and 4 were inspected. This paper gives exact uniform sampling with prescribed hull dimension and explicitly identifies the underlying orbit counts as classical Anzahl formulas. Its Theorem 15 invokes Wan's symplectic counting theorem. The inspected results do not state the arbitrary cross-Gram point law used here. The current work therefore makes no claim to the first uniform sampler or to new orbit sizes for subspaces of a prescribed type.

### Gorodetsky (2026)

Ofir Gorodetsky, *Statistics of entries of matrices from the general linear group over a finite field*, [arXiv:2610.29305](https://arxiv.org/abs/2610.29305).

The title, bibliographic record, and abstract-level description identify this as a related study of entry constraints and asymptotics for the general linear group. The full paper was not inspected in this literature review. No claim about its complete coverage, or about symplectic extensions absent from its abstract, is made here.

## Priority assessment

In the inspected sources, this review did not locate the same arbitrary cross-Gram point law together with its exact support criterion and sharp fixed-dimension correction. It also did not locate the accompanying balanced nonsingular rectangular optimal-test result in the external papers inspected. The closest supplied result is the Article's Lagrangian-target rank-blindness theorem, explicitly acknowledged above.

These findings support presenting the paper as a proved extension of a specific question in the supplied Article. They do **not** certify that every formula or consequence is new to the literature. In particular, full inspection of the older form-representation papers and consultation with specialists remain necessary before an unqualified claim of research priority. The mathematical statements and their proofs do not depend on such a priority claim.
