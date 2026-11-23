# Lean formalization package and exact verification boundary

This packet supplies **candidate proof-producing iPRA source**, explicit geometric
syntax, and a concrete integration route. It does **not** claim a completed Lean
formalization of all the geometry in the report.

## What is present

* `EuclideanIPRA/Derivations.lean` contains 42 theorem declarations: 40 generic
  integer-coordinate proof candidates and two universally closed versions.
  Their result type is `Γ ⊢[PRAAx] φ`. It is not an ambient Lean equality over
  `Real`. The source uses ProveIt's existing `ipra_ring` and `ipra_zle` macros,
  which construct derivations in its intuitionistic arithmetic calculus.
* `EuclideanIPRA/GeometrySyntax.lean` defines a record of **fixed PR program
  syntax** for an algebraic-code backend; exact coded points; metric, incidence
  and order predicates; explicit construction terms; and five representative
  target formulas. No backend instance and no correctness axioms are supplied.
* `../code/check_certificates.py` was executed successfully. It checks 41 scalar
  component identities in the exact polynomial ring over the integers. These
  comprise 37 named relations; vector components are counted separately in the
  machine-readable certificate file. This is not a count of geometric theorems.
* `build_status.json` records the actual validation performed here.

**Lean and Lake were unavailable in this environment. None of the new Lean
files was compiled here.** The source contains no `sorry`, new `axiom`
declarations, or `native_decide`, but absence of those strings is not a
substitute for elaboration and kernel checking. The Python checks establish
only the displayed polynomial identities, not the sign, branch, denominator,
construction, or internal-derivability obligations of the complete report.

## Reused foundation, pinned exactly

Repository: <https://github.com/VladimirReshetnikov/ProveIt>

Commit: `bbb85238dac533fc4b7b84a750cca864fe35fed5`

Lean toolchain: `leanprover/lean4:v4.32.0`

Mathlib commit from that checkout: `81a5d257c8e410db227a6665ed08f64fea08e997`

The root Lake package is `ProveIt`. The library `IPRADerivations` has source
directory `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean`.

The relevant existing modules are:

| Module | Role |
|---|---|
| `ConciseIPRA.PR` | PR symbols, arithmetic terms, defining equations, QF induction |
| `ConciseIPRA.Syntax` / `Deduction` | First-order formulas and intuitionistic derivations |
| `IPRADerivations.Core.Integers` | Signed integer terms as natural-number pairs |
| `IPRADerivations.Core.Tactic` | `ipra_ring`, `closeAll`, and the quotient-ring bridge |
| `IPRADerivations.Core.IntCertificates` | Nonnegative slack certificates and `ipra_zle` |
| `IPRADerivations.Core.Definitions` | `PTm.toPR`, explicit definitions and primitive recursion |
| `IPRADerivations.Core.Search` | Bounded search with object-theory correctness lemmas |

The existing triangle-formula and quadratic-algebra modules are additional
reusable components. They do not, by themselves, constitute an implementation
of an arbitrary-depth real-algebraic root/sign backend.

## How to compile only the new modules

Use an existing checkout at the exact commit above, with the pinned toolchain
and dependencies already installed. Build its required prerequisites once:

```sh
lake build IPRADerivations.Core.IntCertificates IPRADerivations.Core.Definitions
```

From this packet's `lean/` directory run:

```sh
python3 build_in_proveit.py --repo /absolute/path/to/pinned/ProveIt
```

The script checks the commit, relevant source cleanliness and toolchain; reads
the prebuilt dependency environment; then writes only to a separate `build/`
directory. It never fetches, installs, updates, or builds upstream dependencies.
The output `build/result.json` can only say `compiled: true` after every new
module succeeds. The upstream source directory is not edited.

## The formalization sequence

1. **Compile the 42 candidate declarations.** Fix any elaboration issues and
   retain the build log. Inspect `#print axioms` for representative declarations
   in a local audit file; a successful theorem must still return `Prf PRAAx`.
2. **Reify the fixed arithmetic algorithms.** Implement finite polynomial and
   rational-code operations, squarefree reduction, Sturm sequences and the
   bounded interval/root routines described in the report as actual `PR k`
   programs. Use `Core.Definitions` and `Core.Search`; record the numerical
   iteration bounds. There is no uniform primitive-recursive evaluator for all
   arbitrary PR program codes being assumed here.
3. **Prove the algebraic representation laws in iPRA.** Establish validity,
   equality and sign correctness; equivalence/congruence of codes; field laws;
   positive denominator clearing; square-root existence and uniqueness;
   inverse correctness under explicit apartness. A host theorem about real
   numbers is not an adequate replacement for these derivations.
4. **Instantiate `AlgebraicSymbols`.** The syntax definitions then become
   concrete iPRA terms and formulas. Translate each denominator-cleared
   polynomial identity into that representation. Positive multiplier and
   nonzero-denominator lemmas discharge the cancellation steps.
5. **Derive the construction and order results.** Start with `lineMeetSpec`,
   `circumcenterSpec`, `thalesSpec`, `lineCircleSpec` and
   `ptolemyInequalitySpec`. Prove witness validity as well as the displayed
   equations. Extend the same pattern to the remaining statement families in
   the theorem ledger.
6. **Close the formulas and audit them.** Use `closeAll` on the complete
   hypotheses-to-conclusion formula, including validity, distinctness,
   orientation and sign hypotheses. Export only declarations of the form
   `([] : List (Fm PTm 0)) ⊢[PRAAx] closedFormula` as finished object results.

## How the report's theorem families map to code

| Family | Literal syntax / certificate | Remaining internal proof work |
|---|---|---|
| Lines, parallelism, intersection | `onLine`, `parallel`, `lineMeet`; `cramer_x/y` | Apartness, inverse, equality substitution, uniqueness |
| Midpoint, centroid, affine ratios | `midpoint`, `centroid`, `area_interpolation` | Rational denominator and order lemmas |
| Pythagoras and cosine law | `polarization`, `sqdist`, `rightAngle` | Cancel 2; nonnegative root uniqueness for lengths |
| Cauchy and triangle inequalities | `lagrange`, `cauchy_schwarz_squared` | Positivity and unsquaring with sign hypotheses |
| Isometries, reflection, congruence | `reflection_norm`, `perpendicularFoot`, `cosine` | Nonzero lengths, orientation choice, witness isometry |
| Angle sum, SAS/ASA/AAS/AAA | `cosine`, `sineSquared`, `angleEq` | Unit-direction pair operations and ordered half-plane cases |
| Heron, median, Stewart | `heron_coordinate`, `apollonius`, `stewart_affine` | Positive side lengths and factor/square-root branches |
| Triangle centers and nine-point circle | `circumcenter`, `orthocenter`, `incenter`; center identities | Validity, uniqueness, noncollinearity, side-distance signs |
| Thales and circle intersections | `thales_identity`, `lineCirclePlus/Minus` | Discriminant sign, root laws, exact number of solutions |
| Chords, tangency, power, radical axis | `line_circle_expansion`, `radical_axis`, `onCircle` | Vieta, tangent multiplicity, positive length products |
| Ptolemy and cyclic quadrilaterals | `ptolemy_complex_x/y`, `ptolemyInequalitySpec` | Triangle inequality plus ordered cyclic equality case |
| Shoelace and Varignon | `shoelace_triangle`, `varignon_area` | Finite-list summation induction and orientation certificates |
| Spatial metric and volume | `lagrange_three`, `triple_cyclic`, `volume_scaling`, `gram_determinant_three` | Finite decomposition and geometric orientation |
| Constructibility and finite polygon certificates | Fixed PR construction terms and signed inequalities | Trace interpretation, branch verification, finite induction |

## Scope of the raw geometry specifications

The syntax declarations are partial targets, not completed theorem contracts.
`lineMeetSpec` states incidence and `circumcenterSpec` states equidistance;
output validity and uniqueness require separate lemmas. `lineCircleSpec`
asserts membership of the displayed candidates when its discriminant is
nonnegative; completeness, the negative case, and the one-versus-two count
are additional obligations. `thalesSpec` is a squared-distance equivalence
that permits endpoints; its angle interpretation requires nonzero rays.
`angleEq` compares cosines, and using it for the report's interior angle pairs
requires their nonnegative sine branch and the proved scalar laws.

No algebraic record reader, general root-isolation backend, finite construction
trace interpreter, polygon/slab observation routine, or `π_g` observation name
has been implemented in Lean here. Their definitions, bounds, and mathematical
proofs are in the report; the steps above describe how to formalize them.

## Exact polynomial checker: why this is universal, and its limit

The checker stores a polynomial as a dictionary from exponent tuples to exact
integer coefficients. Addition merges coefficients; multiplication performs
finite convolution; powers are repeated multiplication. Zero coefficients are
removed. These operations preserve polynomial evaluation by a direct induction.
Thus equal coefficient dictionaries entail equality under **every** assignment
in **every** commutative ring. No test points, floating point, approximate zeros,
CAS simplification heuristics, or probabilistic polynomial identity test occur.

The normalization implementation itself is not formally verified in this
packet. Its source is short and the complete normal forms are retained in
`../certificates/polynomials.json`, so each result is independently reproducible.
The Lean object-theory module offers the intended independently checked route
through the repository's established proof-producing ring machinery.
