# Formalization roadmap

This document is a specification for future work. No new Lean theorem in
this package has been compiled, and no placeholder Lean proof is supplied.
The selected upstream Lean sources are separately identified as upstream.

## 1. Finite positive interpolation

Formalize a finite symmetric set Γ of real frequencies with minimum gap δ
after adjoining zero. Define the triangular probability density g_A, its
Fourier transform f_A = sinc²(A·/2), and the matrix M(λ,κ)=f_A(λ−κ).

The required statements, in dependency order, are:

1. The convolution of two uniforms on [-A/2,A/2] is g_A, with the stated transform.
2. Separation bounds the sum of reciprocal squared distances by π²/(3δ²).
3. For Aδ≥4π, the induced column-sum norm of M−I and the l1 norm of b=f_A|Γ are at most 1/12.
4. The Neumann inverse exists and its solution a=−M⁻¹b has l1 norm at most 1/11.
5. Uniqueness preserves realness and reflection symmetry.
6. The density g_A(1+Σ aλ exp(−iλt)), after mass normalization, lies between (5/6)g_A and (6/5)g_A and vanishes at all prescribed frequencies in Fourier space.

This part is finite-dimensional linear algebra plus standard real integration.
The exact rational demonstration is useful as a separate computational check,
but does not replace a universal proof.

## 2. Multisets, multiplicities, and damping

Prove greedy coloring of a finite real multiset into K δ-separated colors,
where K is maximum occupancy of a half-open interval of length δ. The
endpoint convention matters: a separation equal to δ permits color reuse.

Formalize convolution support addition, positivity, normalization, Fourier
multiplication, and addition of zero orders. Prove the global inequality
|sinc x|≤sin(1) for |x|≥1. This establishes the explicit finite theorem
H≤4πK/δ+N/B and attenuation (sin 1)^N.

## 3. Optimal support order

Apply the entire-function version of Jensen's formula to a characteristic
function with |F(z)|≤exp(H|Im z|) and F(0)=1. The resulting bound is
H≥(π/(2B))Σ log(B/|λ|), with prescribed multiplicities.

The arithmetic dependencies are the Riemann–von Mangoldt count and, only
for the distinct-only lower constant 5/12, Montgomery's proved squared-sinc
pair formula. The elementary passage D≥(3N−M2)/2 needs only integer
multiplicity arithmetic. Neither simplicity nor the pair-correlation
conjecture may be inserted as an assumption.

## 4. Dirichlet input and prime sums

Import the actual upstream Dirichlet GRH theorem, together with a precise
mapping from Mathlib's L-functions to the analytic functions in the report.
Prove the local zero count uniformly in height for a fixed finite family.

For the ramp signal, formalize Mellin inversion and shift the contour to
Re(s)=−1/4. Keep the residues at 1, at every critical zero, and at zero.
Prove convergence on good horizontal heights and absolute convergence of
the new vertical integral. Treat missing Euler factors by finite geometric
sums. These steps give the sharper O((1+v)exp(−v/2)) remainder.

Finally use absolute uniform Fourier convergence to integrate term by term
against the constructed probability measure. Track the central-zero bias
and the factor exp(u/2) explicitly. Carathéodory supplies the optional
center-dependent finite quadrature after the common kernel is constructed.

## Verification boundary

The report contains complete written proofs of these new statements, with
classical analytic inputs identified. Building only the finite matrix lemma
would not certify the analytic application; building the upstream GRH proof
would not certify the new matrix or averaging theorem. Both interfaces must
be established in any eventual end-to-end formalization.
