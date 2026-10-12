# Claim ledger and proof dependencies

All theorem numbers refer to `article.pdf` / `article.tex`.

| Result | Status | Essential proof input |
|---|---|---|
| Two-index Lambert family | Established prior work; no novelty claim | Broadhurst–Dorigoni (2025), with 2026 overview |
| Mellin representation and symmetry | Proved specialization of standard input | Absolute convergence, Mellin inversion |
| Theorem 3.1: triple-pole cancellation and uniform expansion | Conventional proof included | Fixed cluster contour, Gamma residues, vertical decay |
| Theorem 3.2: centered all-order logarithmic jets | Proved explicit refinement | Analytic Gamma/zeta normalizers, finite coefficient extraction |
| Theorem 4.2: hypergeometric arithmetic Borel kernel | Proved specialization/refinement of known infrastructure | Zeta reflection, hypergeometric coefficients, normal convergence |
| Theorem 4.3: restored odd second-jet sector and pi^2/2 jump ratio | Proved explicit jet identity | Double trivial zeros, artanh kernel, branch signs |
| Theorem 5.1: exact scalar real completion | Proved specialization; not a new general Lambert transformation | Log-kernel Mellin identity, functional equation, contour shift |
| Theorem 6.1: uniform arcsinh core inverse with three corrections | Proved proposed inverse refinement | Centered triple collision, analytic implicit function theorem |
| Theorem 6.2: first exponential correction to actual positive inverse | Proved | Uniform finite remainder, derivative lower bound |
| Theorem 6.3: displaced simple folds | Proved for the singular CORE only | Two-equation implicit function theorem, local quadratic preparation |
| Theorem 7.1: all inverse coefficients, signs, degree, Catalan term, valuations | Proved proposed coefficient calculus | Formal Lagrange inversion with finite coefficient support |
| Theorem 7.2: ordinary radius zero; exact inverse Borel radius 4*pi^2 | Proved | Sign noncancellation, factorial composition estimate |
| Theorem 7.4: physical finite-sector expansion | Proved at every fixed order | Exact residual transport, core derivative of order X |
| Theorem 8.1: exact all-order inverse lateral transport | Proved, convergent in auxiliary Stokes parameter | Rouché domain, analytic Lagrange–Bürmann formula |
| Theorem 8.2: nested inverse splitting and averaging defect coefficient -1 | Proved proposed explicit consequence | Exact arithmetic jump, differentiated inverse transport |
| Section 11 hyperbolic large-order amplitudes | CONJECTURAL | Fixed-factor heuristic; uniform factor-count control missing |
| Global analytic continuation of inverse Borel transform | NOT PROVED here | Future work |
| Full Lambert-function complex fold displacement | NOT PROVED here | Article proves core folds only |

## Evidence levels

The infinite assertions rest on written conventional proofs. SymPy checks only
finitely many exact identities (through eight inverse sectors). mpmath and SciPy
provide non-interval numerical diagnostics. No proof-assistant compilation or
independent peer review was performed. The detailed inverse/jet refinements are
proposed contributions, not certified assertions of worldwide priority.

## Dependency outline

```text
Mellin representation
  -> triple collision -> centered jet generator
       -> scaled analytic core -> arcsinh crossover -> core folds
       -> uniform residual -> actual crossover correction
  -> zeta reflection -> arithmetic Borel kernel
       -> second-jet parity identity
       -> exact real completion -> arithmetic E1 jump
  -> rational resonant coefficients
       -> formal Lagrange formula -> signs/valuations/Catalan degree
       -> factorial composition bound -> exact Borel radius
       -> physical finite-sector inverse
Exact real completion + analytic Lagrange transport
  -> full inverse lateral jump formula
  -> nested first action and second-action arithmetic-averaging defect
```
