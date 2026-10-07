# Proof audit and status

This is a record of self-checks, not an independent review or formal proof.

## Dependency graph

Canonical cube identity -> cubic projective loss -> derivative periods ->
canonical cap and inactive-slice deficit.

Boolean coefficient criterion -> exact relative gluing.

Inactive-slice equality + relative gluing + four-point energy identity ->
complete endpoint-function classification.

Published Eisner--Tao near-extremizer theorem -> polynomial phases on each coset
-> a bounded-degree and bounded-torsion mixed defect -> exact relative repair
-> dimension-independent entry into the classified family.

Four-point / character counts -> complete transverse Hessian -> finite-product
bounded-function coercivity -> sharp leading stability coefficient.

The prior all-degree **tensor** theorem is needed only for the final corollary
that begins with an unspecified nonintegrable tensor. The canonical function
classification and its stability theorem do not require that tensor theorem.

## Critical checks

### Normalizations and phases

Every measure is normalized. The energy is a selected Fourier coefficient
squared, not a Gowers norm raised to an unspecified power. It equals the
weighted d-cube average. A primitive of an integrable correction has additive
top derivative S/2. Its phase multiplication cancels the sign (-1)^S exactly.

The coefficient in the stability theorem refers to **squared** L2 distance.
In the sharpness example, the perturbation is exp(i*t*chi_v), with t in radians,
whereas e(theta*|u|) uses theta in turns. This yields cos(2^d*t) in the energy.

### Genuine derivative constraints

At the endpoint, the retained index-four slice slack forces all derivatives
in R = ker(u) intersect ker(v) to have degree at most d-2. The remaining
sampled directions are arbitrary ambient directions, not just R directions.
That distinction is necessary for exact gluing at degree d-1.

The tested function is not assumed to ignore inactive coordinates. Only after
a proved polynomial gauge is removed is a four-point quotient used.

### Binary optimization

The full signed direction count gives a trigonometric identity for arbitrary
unit phases, not just for roots of unity. For d >= 4 it is strictly increasing
in the two transverse cosine variables. The third variable is genuinely free
at equality. The proof directly places the rounded phase in the claimed
extremizer family, so no circular appeal to the later classification is needed.

### Uniform entry, not fixed-dimensional compactness

Separate coset polynomial approximations are not assumed to glue. Their
constant phases are first removed. The piecewise polynomial then has degree
at most d-1+c and takes values in a fixed dyadic grid. Its mixed derivative
is a polynomial on the space of all cube parameters. A nonzero polynomial's
support and the smallest nonzero grid angle give a positive detection gap.
A sufficiently small test error thus implies exact repair. The codimension is
fixed; the ambient dimension is unrestricted.

Eisner--Tao is imported explicitly for the uniform approximation modulus. A
numerical value of that modulus, a numerical global entry threshold, and the
optimal global all-deficit constant are not claimed.

### Hessian and bounded-function remainder

The two kernel directions are the tangent directions 1 and chi_u. A nearest
extremizer exists because its family is a finite union of compact tori.
Differentiating distance only along that torus removes these two components of
the imaginary error. No smooth parametrization of the tested function is used.

The disk constraint gives r^2 <= 2A, where A is the mean loss in real part.
The exact finite-product expansion is used for all higher-order terms. Three
distinct Boolean cube vertices are independent even though particular sampled
cubes may be degenerate. The weight is bounded in modulus before applying that
independence; independence of the weight and the vertices is not asserted.
Rare, large errors and zeros are therefore covered. A pointwise Taylor bound
is not substituted for a normalized-L2 estimate.

### Sharpness

On F_2^2 the exact energy deficit of an appropriate transverse character is
m_d*(1-cos(2^d*t))/4^d. For small t the nearest component is the original torus,
and its exact squared distance is 2*(1-cos t). Their ratio tends to 2/m_d.
This matches the all-dimensional upper bound and proves optimality of the
leading coefficient, not optimality of the displayed remainder constant.

## Executed checks

Both of these ran successfully and produced identical JSON:

    python3 code/verify.py --output data/verification.json
    python3 -O code/verify.py --output data/verification_optimized.json

See the JSON for exact counts. The checker covers coefficient normal forms,
relative gluing certificates, exact cyclotomic energy identities, inactive
coordinates, arbitrary Gaussian-rational bounded functions, and the Hessian's
symbolic cosine parameter. It uses no assertion that optimization disables.

The checker is not a proof that every complex function in every dimension obeys
the inequalities. Those quantifiers are handled by the written proofs.

The article was compiled with latexmk/pdflatex, all references resolved, and all
pages were rendered and inspected for layout. No proof assistant was run.

## Remaining mathematical limits

- Main function classification and sharp stability require d >= 4.
- Cubic equality is analyzed only on the binary quotient, not in all dimensions.
- No noncanonical second extremal value or direct-sum formula is proved.
- No localization theorem, arbitrary-selector construction, or improved global
  progression/Szemeredi bound is claimed.
- The paper is unrefereed; external novelty is not established.
