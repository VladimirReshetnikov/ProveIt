# Proposed formalization and integration obligations

This is a plan, not a report of a successful Lean implementation. No new Lean
code is shipped or represented as compiled. Begin with a cyclic finite-set
companion under the repository's existing conventions; general finite abelian
groups and torus characters can be a subsequent generalization.

## Mathematical interfaces

### 1. `bohr_escape_tubes_card_le` (proposed name)

Inputs: `N > 0`, finite frequency set K, positive integer m,
`0 < rho <= 1/4`, `d ∈ bohr K (rho/(2*m))`.

Output:

    2*m*(|B| - |B ∩ (B+d)|) <= |bohr K (3*rho/2)| - |B|,
    where B = bohr K rho.

Keep a stronger intermediate theorem with the actual character displacement in
each coordinate. For natural subtraction, establish the relevant inclusions or
cardinality inequalities first; an equivalent additive cardinality statement
can avoid truncated-subtraction issues.

Core proof obligations:

- The two exit sets have equal size, equal to the overlap defect.
- A witnessed exit cannot return for 1 through 2m steps.
- Same-sign tube collisions contradict non-return at a difference of indices.
- Opposite-sign collisions contradict non-return at the sum of indices.
- All tubes lie in the enlarged Bohr set and outside the original.
- All endpoint conventions are respected, including rho = 1/4.

The central lifted scalar implication is:

    |a| <= rho, |v| <= rho/(2m), |a+v| > rho
      => rho < |a+jv| <= 1/2 for 1 <= j <= 2m.

Use the sign forced by the witnessed exit. A plain triangle inequality does
not prove the lower bound and should not be substituted for the sign argument.

### 2. `bohr_three_halves_card_le` (proposed name)

Output: `|bohr K (3*rho/2)| <= 3^|K| * |bohr K rho|`.

Partition each centered coordinate interval into three disjoint cells of
diameter at most rho. Give an explicit endpoint assignment. Translate each
nonempty cell to inject it into B. Count points of the original finite group,
not only distinct coordinate images, since the character map can have a kernel.

### 3. `bohr_fixed_radius_overlap` (proposed name)

Combine the previous two statements to give coefficient
`(3^|K|-1)/(2m)`. This should be an additional theorem, not a silent alteration
of the old declaration on its wider radius range.

### 4. `dense_domain_freiman_extension` (proposed name)

Finite-set inputs A ⊆ B, |B| > 0, hole fraction eta, overlap defect bound kappa
on C, Freiman-2 map psi on A, integer k >= 2, and

    (2k-1)*kappa + 2k*eta < 1.

Output: C ⊆ A-A and a uniquely induced Freiman-k difference map on C.

Prove a reusable tree-intersection cardinality budget first. Use formal vertex
labels even when positions coincide in the group. Before implementation,
check the exact equivalence between tuple relations allowing repetitions and
the repository's `FreimanHom` API. The mathematical proof must not be weakened
to distinct-element relations.

### 5. Radius corollaries

For r = |K| >= 1 and c = 3^r-1:

- m = 4c gives radius rho/(8c), defect <= 1/8, pair overlap >= 5/8
  at density 7/8, and four-vertex base-point mass >= 1/8.
- m = 3c+1 gives radius rho/(6c+2), defect < 1/6, and extension with
  four-vertex mass >= 1/(6c+2). It does not preserve the 5/8 pair margin.

### 6. Finite-fibre compatibility

Preserve the actual direction-set size |A| in the exception count:

    2*(1-sigma)*|A| > (1+kappa)*|B|.

With nonempty common target fibres and 0 <= theta < 1/2, the two local-value
sets intersect. If |A| >= 7|B|/8, kappa <= 1/8, and sigma = sqrt(theta), then
sqrt(theta) < 5/14 suffices. This is a sufficient threshold, not claimed optimal.

## Edge cases

- K empty: B is the whole group and all defects vanish; the radius formulas
  with 3^r-1 in a denominator require a separate nonempty-K premise.
- d in the common character kernel: both escape sets are empty.
- Very small ambient groups and low-order d: non-return forces empty exits;
  no prime-modulus or high-order assumption should be added unnecessarily.
- rho = 1/4: the lifted 2m-th point may equal 1/2, still outside the strip.
- Closed Bohr boundaries: strict escape is necessary in the lower inequality.
- Repeated path vertices and total path sum zero: preserve formal labels.
- Empty target fibres in compatibility: relative statements may be vacuous;
  explicit nonemptiness is required.
- Strict budget boundary: the proof needs positive residual mass, not >= 0.

## Validation after implementation

Record the exact toolchain and Mathlib versions, build commands, exit status,
and theorem names. Run the repository's axiom audit. Only after actual kernel
checking should the formalization ledger be changed. This package performed
none of those future steps and did not modify the repository.
