# Theorem map and scope

This map refers to the accompanying manuscript, not to external theorem numbers.
Its purpose is to distinguish the new conclusions from their established inputs.

| Result | Manuscript location | Established input | Added conclusion |
| --- | --- | --- | --- |
| Convergent angular reconstruction | Theorem 3.1; label `ang:thm:sum` | Harmonic depth-two kernel and angular uniqueness; analytic Lagrange inversion | A complex norm makes the scalar-coupling degree expansion absolutely convergent for every real `a >= 6`, `b > 0`, `0 < rho <= 1`, with an explicit uniform error bound |
| Exact summation order | Theorem 3.2; label `ang:thm:Abel` | Source multiset coefficient formula | Abel limit within each fixed nonlinear degree followed by an ordinary convergent degree sum reconstructs the boundary displacement |
| Fixed period algebra | Corollary 4.2; label `ang:cor:algebra` | Differentiation/lowering identities and rational nonpositive-order polylogarithms | All integer-order degree blocks lie in one fixed finite algebra of depth-two and ordinary polylogarithm values at `i` |
| Explicit finite approximation | Theorem 5.1; label `ang:thm:finite` | Finite Fourier truncation and coefficient extraction | A quantitative two-term error bound for frequency and nonlinear-degree cutoffs |
| Gaussian accuracy | Theorem 5.2; label `ang:thm:gaussian` | Theorem 5.1 | A finite construction with error `exp(-lambda*a^2 + O_lambda(a))` for every `0 < lambda < log(3/2)` |
| Sharp Lambert amplitudes | Theorem 6.1; label `lm:thm:sharp` | The incoming report's exact forward coefficients and finite inverse formula | Proof of the named even/odd amplitude conjectures, with a locally uniform additive remainder for complex coupling |
| Analytic-core universality | Theorem 6.2; label `lm:thm:universal` | Formal Lagrange inversion; factorial convolution inequalities | A two-action leading-amplitude law independent of nonlinear core changes and of finite changes to forward coefficients of order at least two |
| First late correction | Theorem 6.4; label `lm:thm:first` | The same exact coefficient formula | The complete next term and a uniform remainder, identifying the effects of the quadratic core and the second forward coefficient |
| Nearest Borel endpoints | Corollary 6.5; label `lm:cor:logs` | Theorem 6.1; the logarithm power series | An exact logarithmic decomposition with a continuous remainder and exact radius `4*pi^2` for every nonzero complex coupling |
| Dilogarithmic correction | Corollary 6.6; label `lm:cor:dilog` | Theorem 6.4; the dilogarithm power series | An explicit log–dilog decomposition with remainder and first derivative continuous on the closed initial Borel disk |
| Minimal direct-inverse ramification | Theorem 7.1; label `ep:thm:classification` | Classical Jonquière expansion and the repository's noninteger local charts | For noninteger `s-1=p/q` in lowest terms the minimal degree is `min(p,q)`; irrational and resonant integer orders are not resolved by any finite cover; holomorphic endpoints occur exactly at `s=1+1/q` |
| Exceptional Taylor coefficients | Proposition 7.3; label `ep:prop:coefficients` | Convergent exceptional chart; Lagrange–Bürmann inversion | Finite coefficient formula, arithmetic support restriction, and explicit examples |
| Failed proposed cut extension | Proposition 7.4; label `ep:prop:cut-counterexample` | Jonquière expansion and elementary zeta sign bounds | Negative answer to the all-real-order extension for `1<s<3/2`, with an exact local threshold at `s=3/2` |

## Essential qualifications

- The angular summation uses the original multiset's nonlinear degree and radial
  degree. It is not a summation functional defined only from coefficients already
  grouped by exponential base. Absolute convergence of its outer degree blocks
  does not establish absolute convergence of the flattened multiset family.
- The existing divergence theorem remains valid. The moving finite construction
  proves an attainable error scale; sharp optimal truncation in the original
  exponential-base ordering remains open.
- The finite algebra of period values is a generating algebra. No algebraic
  independence, minimal generator set, or reduction of every depth-two value to
  classical polylogarithms is asserted.
- The general factorial composition/reversion framework is established in the
  literature. The contribution is the specific uniform proof and explicit
  refinements described here, rather than a claim to invent that framework.
- A vanishing even or odd leading amplitude at a complex coupling does not remove
  an individual Borel action: both exponential action multipliers are nonzero
  whenever the coupling is nonzero.
- The Borel identities describe a holomorphic germ in its initial disk and
  regularity of the remainder on the circle. They do not provide analytic
  continuation outside that disk, a complete singularity set, Stokes constants
  on subsequent sheets, or Borel summability along a singular direction.
- Endpoint ramification is local to the branch continued along the positive real
  interval. It does not determine the Taylor radius of the inverse at zero or
  all global singularities. A holomorphic continuation through the image of a
  cut need not remain an inverse of the principal forward branch on both sides.
- The failed cut inequality is the all-real extension of an integer-order
  ingredient suggested by the further-research question on endpoint circles.
  That broader endpoint-circle/radius question is not settled by this
  counterexample alone. The audited integer theorem is correct and is preserved.
- Ordinary numerical diagnostics and exact finite algebra checks supplement the
  analytic proofs. None of the programs is a proof-assistant formalization or an
  interval-certified analytic proof.

## Further work

The article develops thirteen research questions: least angular convergence
threshold; sharp optimal truncation; comparison of summation prescriptions;
period-algebra reduction; other colors and depths; full inverse Borel
continuation; all relative late terms; physical moving-parameter limits;
parity-amplitude cancellation; global cut-modulus range; global singularities at
exceptional orders; direct versus feedback ramification; and formalization of
the reusable finite algebra.
