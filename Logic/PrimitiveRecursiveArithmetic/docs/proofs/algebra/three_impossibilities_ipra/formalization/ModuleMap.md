# Lean module map and completion criteria

## Foundation already present in ConciseIPRA

Use the pinned ProveIt revision listed in `provenance/SOURCES.md`.

- `PR.lean`: `PR`, `PTm`, `PRAAx`, and `PRA.qfInd`.
- `NativeBiInterpretation.lean`: `native_iff_pra`, `pra_iff_native`, round trips, and equiconsistency.
- Existing native logic, equality, normalization, and proof-checker infrastructure.

## New modules

### 1. `ClassicalConstructions/Coding/Basic.lean`

Deliverables:

- canonical integer, rational, list, vector, and finite-map codes;
- bounded minimization and finite folds;
- graph formulas and representability proofs for each primitive-recursive operation.

Completion test: every exported function has a `PRAAx` graph theorem and no meta-level classical dependency.

### 2. `.../Coding/Polynomial.lean`

Deliverables:

- integer/rational polynomials;
- trim, degree, evaluation, derivative, multiplication, powers;
- pseudo-division, subresultants, gcd, square-free factorization;
- Sylvester resultant and its Bezout/evaluation properties.

Completion test: the resultant step used in circle squaring and the gcd steps used in root isolation produce checkable certificates.

### 3. `.../Coding/Matrix.lean`

Deliverables:

- fraction-free row reduction;
- rank and solution certificates;
- greedy basis theorem over coded decidable fields.

Completion test: the constructive tower-law divisibility theorem can use this module without any existence-only basis theorem.

### 4. `.../Algebra/QuadraticTower.lean`

Deliverables:

- normalized tower elements;
- field operations and zero testing;
- displayed basis of size `2^e`;
- subfield degree divisibility via a greedy basis over `Q[alpha]`.

Completion test: closed theorem that no irreducible cubic root occurs in a tower certificate.

### 5. `.../Geometry/Trace.lean`

Deliverables:

- point/line/circle instruction syntax;
- branch-selected intersection verifier;
- line-line, line-circle, circle-circle coordinate formulas;
- extraction of a quadratic-tower certificate.

Completion test: replaying any accepted trace produces exact coordinates and a proof that every coordinate lies in the final tower.

### 6. `.../Geometry/CubicObstructions.lean`

Deliverables:

- rational-root theorem for monic cubics;
- irreducibility of `X^3 - 2` and `X^3 - 3X - 1`;
- complex multiplication/triple-angle calculation;
- closed cube and 60-degree trisection impossibility formulas.

Completion test: both theorems compile before any analysis or transcendence modules are imported.

### 7. `.../Analysis/PRReal.lean`

Deliverables:

- rational interval/Cauchy names with explicit moduli;
- ring operations and exact-equality formula;
- factorial-series `exp`, `sin`, `cos`;
- alternating-series `atan`;
- fixed-function Riemann sums and a fundamental theorem with explicit derivative modulus.

Completion test: no quantified completeness axiom for arbitrary real functions is used.

### 8. `.../Analysis/PiArea.lean`

Deliverables:

- `pi := 4 * atan 1`;
- Machin identity as an efficient alternate name;
- `exp(i*pi) = -1`;
- rational substitution for the quarter-disk integral;
- unit-disk area equals `pi`.

Completion test: equality is proved between coded Cauchy names with a common modulus.

### 9. `.../Algebra/RootIsolation.lean`

Deliverables:

- Cauchy root bound;
- explicit root-separation bound;
- Sturm-Cauchy index on a rational segment;
- root count on rational rectangles;
- finite disjoint isolating boxes with multiplicity;
- exact equality and arithmetic for algebraic codes.

Completion test: from `G(i*pi)=0`, the procedure identifies a box/index for `i*pi` using the separation bound and the fixed Cauchy name.

### 10. `.../Transcendence/SymmetricSubsetSums.lean`

Deliverables:

- effective symmetric-polynomial reduction;
- Vieta substitution for a nonmonic polynomial;
- subset-sum product polynomial over `Q`;
- exact zero-root count, division by `Y^K`, denominator clearing.

Completion test: output polynomial roots, with multiplicity, coincide with all nonzero subset sums.

### 11. `.../Transcendence/Hermite.lean`

Deliverables:

- `h_p`, `A_p`, `n_p`, `g_p`;
- derivative divisibility and `n_p mod p`;
- power-sum integrality for scaled roots;
- coefficient/root bound `C`;
- explicit factorial threshold;
- least-prime-divisor search on `H! + 1`;
- final integer `N`, `abs N < 1`, and `N != 0 mod p`.

Completion test: a closed object-level theorem `NoPositiveIntegerExpRelation` under `PRAAx`.

### 12. `.../Transcendence/Pi.lean`

Deliverables:

- even/odd transform from `P(pi)=0` to `G(i*pi)=0`;
- root enumeration and subset-sum relation;
- invocation of Hermite contradiction;
- closed transcendence negation for the fixed `pi` name.

Completion test: `#print axioms` for the meta-theorem contains only Lean's logical kernel axioms, while the theorem's conclusion is an explicit `PRAAx` derivability statement.

### 13. `.../Geometry/Impossibilities.lean`

Deliverables:

- all three closed `PRAAx` theorems;
- conjunction or native macro packaging;
- transport through `pra_iff_native`.

Completion test: the small native checker accepts an exported certificate for the combined theorem.

## Suggested order

1. Cubic path through modules 1-6.
2. Fixed pi/area path through modules 7-8.
3. Root isolation and symmetric algebra, modules 9-10.
4. Hermite integer contradiction, module 11.
5. Assembly and native bridge, modules 12-13.
