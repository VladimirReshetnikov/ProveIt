# Definitions and remaining proof obligations

## 1. Logical target

Use the repository's intuitionistic first-order calculus `Prf PRAAx` with
quantifier-free induction and symbols for fixed primitive recursive
functions. The final theorem is a scheme over fixed PR presentations of
the metric and its jets, with ordinary numerical mesh and precision inputs.
Equivalently, a finite certificate theorem can quantify uniformly over
integer-coded input tables. Do not assert a total PR evaluator for arbitrary
PR program codes. A generic evaluator must be supplied with a numerical
clock, with correctness proved for each fixed program.

Keep the following three claims separate:

1. An ambient Lean statement about rational arrays or real manifolds.
2. A Lean value inhabiting `Γ ⊢[PRAAx] φ`.
3. A meta-theorem that a family of such numerical formulas represents a
   smooth analytic theorem under specified real-name contracts.

## 2. Encoded arithmetic

Use naturals as the object-language domain. A signed integer is a pair
`(a,b)` representing `a-b`; rational data are `(a,b,d)` representing
`(a-b)/(d+1)`. Equality, order, addition, multiplication, and absolute error
are decided by cross multiplication of positive denominators. Reduction to
lowest terms is unnecessary. Lists use a fixed PR pairing and PR bounded
projection, with explicit length. All folds have a numerical iteration bound.

Define `qerr x y n` as the two natural inequalities expressing
`|x-y| <= 2^(-n)`. A fast Cauchy name is a fixed PR rational-valued symbol
`a(n)` with the universal contract
`|a(n)-a(m)| <= 2^(-n)+2^(-m)`.
This contract is an assumption/formula family; the proof never performs
induction on that quantified formula. Equality of named values means
arbitrarily small rational error with an explicit reindexing function.

## 3. Finite surface data

Use a bounded list of ordered triples of distinct vertex identifiers.
Each unoriented edge occurs once or twice. Face orientations are local only:
the surface may be nonorientable. For a globally oriented specialization,
require occurrences in a double edge to have opposite directions. Reject
duplicate unoriented triangles. For each vertex
form its finite link graph. The link is a single cycle (interior vertex) or
a single path (boundary vertex), certified by an explicit ordered traversal.
The certificate includes traversal positions, so checking does not invoke
unbounded graph search. Connectedness of the whole surface is optional.

Derive from these finite checks:

- double counting triangle sides: `3F = 2Ei + Eb`;
- two boundary incidences at each boundary vertex: `Eb = Vb`;
- repartitioning the same corner table by faces or vertices;
- repartitioning the half-edge table by interior pairs and boundary edges.

Each proof uses a running counter invariant. For example, after processing
the first j half-edges, the number processed equals the sum of the partial
edge-incidence counters. This invariant is a numerical equation, hence
quantifier free. The final finite inequalities use common denominators.

## 4. Analytic names and jets

For each face use the reference triangle with vertices `(0,0),(1,0),(0,1)`.
One convenient primitive presentation uses a positive triangular coframe
`theta1 = a dx + b dy`, `theta2 = c dy`, with fixed PR rational names for
a,b,c and their partial derivatives through order two at rational points.
The induced metric is `g = theta1^2 + theta2^2`. Data include:

- an integer H>=1 with a,c>=1/H and absolute values of all needed coframe
  jets at most H, giving explicit positive metric bounds;
- PR uniform continuity moduli for the highest derivatives;
- first-order Taylor remainder contracts for the lower jets;
- a finite gluing description with tangent/metric compatibility sufficient
  for inward-conormal geodesic-curvature cancellation;
- explicit cyclic tangent-sector data at interior vertices and path-sector
  data at boundary vertices, with quantitative nondegeneracy.

An equivalent convenient interface supplies the derived coframe,
connection coefficients and their derivatives, **together with proofs**
that they are computed from the metric jets. Supplying these values without
that proof would leave an unchecked geometric assumption.

## 5. Finite analytic primitives

Formalize these in this order:

1. Rational reciprocal and square-root approximations with explicit
   positive denominator/lower-bound hypotheses.
2. Pi and arctangent names by rational series/range reduction or by
   explicitly bounded rational quadrature.
3. Uniform grid quadrature and Cauchy comparison using supplied moduli.
4. The one-dimensional Taylor-cell estimate and `TaggedFTC` telescoping.
5. The two-dimensional triangular Green identity by finite horizontal and
   vertical slicing, with a common rational grid and explicit boundary
   weights. No general Stokes theorem is presumed.
6. The local coframe/connection curvature identity by rational differential
   algebra, including its sign convention.
7. The tangent-angle derivative and corner-turn identities, using the
   explicit positive triangular frame to avoid any global angle choice.
8. The metric-corner angle sum at each supplied tangent fan.

All derivatives in this list are encoded by Taylor remainder contracts at
rational points. Products and quotients use rational lower bounds. Every
mesh size and evaluation precision is a fixed PR expression in the requested
accuracy, the finite counts, and the presentation's bound/modulus functions.

## 6. Assembly and precision

For one rational approximation `p` to pi, let C be total face curvature, B
the sum on boundary edges, I the sum of the paired interior half-edges, A
the total corner-angle sum and Theta the boundary exterior-angle sum. Set

    R = C + B + I + F p - A,
    S = A + Theta - (2 Vi + Vb) p.

The exact identity is

    C + B + Theta - 2 p chi = R - I + S.

If face residuals are bounded by `ef`, interior pair residuals by `ee`,
interior vertex residuals by `ev`, and boundary vertex residuals by `eb`,
then

    |defect| <= F ef + Ei ee + Vi ev + Vb eb.

For a common residual bound `2^(-q)`, set
`M = max(1,F+Ei+Vi+Vb)` and
`q = n+2+ceil_log2(M)`. This spends at most `2^(-n-2)` on residual assembly;
the remaining budget covers the individual quadrature/name conversions
and the approximation of `2*pi*chi`. Every contribution must be accounted
for explicitly; a common precision index must not silently disregard the
factor `2*abs(chi)` multiplying the pi error.

To prove each sum bound in iPRA, replace a signed value by positive/negative
parts and use the QF invariant

    sumPositive(j) <= sumNegative(j) + j*errorNumerator

after clearing denominators. The reverse inequality is treated separately.
Use guarded induction `j <= N -> invariant(j)` as in `TaggedFTC.lean`.
The universal local contracts are instantiated to obtain the step's cell
hypothesis; they are not part of the induction formula.

## 7. Final deliverable to formalize

For every fixed admissible PR presentation, construct a PR rational function
`Total(n)` and explicit reindexing/mesh functions. Derive in iPRA, from the
presentation contracts, the two inequalities constituting

    |Total(n) - 2*p(n')*chi| <= 2^(-n),

with the chosen precision `n'` displayed. Then prove the interpretation lemma
that `Total` names `integral K dA + integral_boundary kg ds + sum corners`.
Do not claim that an arbitrary abstract C2 manifold yields this input data,
a triangulation, a positive lower bound, or a PR modulus inside iPRA.
