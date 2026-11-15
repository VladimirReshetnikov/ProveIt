# Lean formalization plan

## Target

For each fixed primitive-recursive presentation of a curve or lamina, produce:

1. a semantic theorem about quotient-free regular interval names;
2. a coded precision theorem in ordinary iPRA, as a derivation
   `[] ⊢[PRAAx] phi`;
3. the translated theorem in the concise scalar theory `TeqAx`, using the
   existing `FromPRA.interp.sound` or `pra_theorem_iff` interface.

Pinned ProveIt commit:
`8c135f6f2a9d041cde785a1a632c44ad98065b20`.

## Dependency graph

```text
Code
  -> Rational/Dyadic arithmetic
  -> finite lists, folds, common-grid refinement
  -> IntervalReal
       -> Sqrt
       -> Circle
            -> SegmentFrustum -> PolygonSurface
       -> CellShell -> GridLamina
  -> LimitTransfer
       -> SurfacePresentation -> SurfacePappus
       -> LaminaPresentation  -> VolumePappus
  -> PR encodings and qf graph formulas
       -> PRAAx derivations
            -> FromPRA.interp.sound
                 -> TeqAx derivations
```

## Phase 1: semantic data and arithmetic

### 1.1 Coded finite data

Define executable structures for:

- signed rationals and dyadics;
- rational points in the meridional half-plane;
- segment lists;
- dyadic cells and finite cell unions;
- fixed-size and length-coded lists.

Prove decoder/encoder round trips and finite fold lemmas.  Reuse Mathlib only
at the semantic layer; object-level functions will later be rebuilt from `PR`.

### 1.2 Quotient-free regular reals

Use nested rational intervals:

```lean
structure RegularName where
  lower upper : Nat -> Rat
  lower_mono : ...
  upper_mono : ...
  nonempty   : ...
  width      : upper k - lower k <= 2^(-k)
```

Implement:

- equality by shifted midpoint or interval overlap;
- addition, negation, bounded multiplication;
- magnitude-bound records;
- diagonal limits from an explicit Cauchy modulus;
- reciprocal with a supplied positive rational lower witness.

Avoid quotients and classical completion.  Every operation should return both
an executable name and its regularity proof.

### 1.3 Square root

For nonnegative rational input, bounded bisection maintains
`lo^2 <= q <= hi^2`.  Prove:

- nesting;
- width after the requested fixed number of steps;
- represented equality of the resulting name squared with `q`;
- monotonicity and a Lipschitz estimate sufficient for the circle recurrence.

## Phase 2: circle constant

Formalize:

```text
N_m = 2^(m+2)
c_0 = sqrt(1/2)
c_(m+1) = sqrt((1+c_m)/2)
s_m = sqrt(1-c_m^2)
p_m = 2*N_m*s_m
q_m = p_m/c_m
```

Required terminal lemmas:

- `1/2 <= c_m <= 1`;
- `1-c_m <= 2^(-m)`;
- `p_m <= p_(m+1) <= q_(m+1) <= q_m <= 8`;
- `q_m-p_m <= 8*2^(-m)`;
- analogous area brackets;
- the perimeter limit `tau` equals twice the area limit `pi`;
- `tau < 8` and a positive lower bound.

All induction predicates can be denominator-cleared, quantifier-free
inequalities.

## Phase 3: finite surface theorem

For a segment with rational endpoints:

1. construct its represented length by square root;
2. prove the midpoint radial moment formula;
3. define the inscribed polyhedral-frustum area
   `Sminus_m = p_m/2 * (r0+r1) * h_m`, where
   `h_m^2 = dz^2 + c_m^2*dr^2`;
4. define the circumscribed area
   `Splus_m = q_m/2 * (r0+r1) * length`;
5. prove nesting and the explicit gap
   `Splus_m-Sminus_m <= 4*(r0+r1)*(length+|dr|)*2^(-m)`;
6. identify the common limit with `tau` times the segment moment.

Then fold over segment lists.  `lean/PappusFinite.lean` already contains the
algebraic list theorem once the one-segment identity is available.

For geometric, rather than multiplicity-counted, area, add a separate simple
polygonal-chain certificate and prove that distinct generated faces meet only
on boundaries.

## Phase 4: finite volume theorem

For a cell `[a,b] x [c,d]`, prove by `ring` after denominator clearing:

```text
((b^2-a^2)/2)*(d-c)
  = ((a+b)/2)*(b-a)*(d-c).
```

Connect disk-area polygon brackets to annular-prism volume, and fold over an
interior-disjoint cell list.  Implement common-grid refinement so subtraction
of nested cell unions is a finite list operation with a disjointness proof.

`lean/PappusFinite.lean` already proves the field-level cell and list
identities.

## Phase 5: explicit limit transfer

Implement a generic lemma:

```text
x_n = c*y_n for all n
x_n -> x with modulus mux
y_n -> y with modulus muy
|c| <= C
--------------------------------
x = c*y
```

The proof should compute one stage from `k`, `mux`, `muy`, and a power-of-two
bound on `C`.  Specialize it to:

- polygonal surface sequences;
- inner/outer cell moment and volume brackets.

Positive division then gives the centroid forms.

## Phase 6: bridges

### Effective piecewise-C1 curves

Formalize the supplied Taylor remainder estimate, chord-speed inequality,
length convergence, and moment convergence.  Rationalize mesh vertices at a
precision whose total perturbation is explicitly bounded.

### Effective Jordan laminas

Define a boundary-cover presentation with:

- a finite dyadic boundary cover of total area at most `2^-n`;
- inside/outside labels away from the cover;
- refinement coherence.

Construct nested inner/outer unions and prove area, moment, and volume gap
bounds.  A later project can derive this presentation from a smooth Jordan
curve plus a separation/winding certificate.

## Phase 7: arithmetization in `PRAAx`

Reimplement each fixed executable function as a `PR` symbol.  Use:

- `PRA.precZero` and `PRA.precSucc` for folds and bisection;
- `PRA.qfInd` for all numerical invariants;
- graph formulas with every existential witness named by a primitive-recursive
  term;
- integer cross multiplication instead of field-valued formulas.

Terminal statements should have a quantifier-free precision matrix, universally
closed over `k`.

## Phase 8: translation to `TeqAx`

After obtaining:

```lean
surface_pappus_pra : [] ⊢[PRAAx] SurfaceSentence
volume_pappus_pra  : [] ⊢[PRAAx] VolumeSentence
```

transport them with:

```lean
FromPRA.interp.sound surface_pappus_pra
FromPRA.interp.sound volume_pappus_pra
```

or invoke `pra_theorem_iff` from `ConciseIPRA.BiInterpretation`.

## Completion audit

A completed development should report:

- no `sorry` or untracked axioms in the final dependency cone;
- `#print axioms` for semantic theorems;
- exact paths and commit hash;
- successful `lake env lean` commands;
- executable agreement tests against `code/pappus_checker.py`;
- a list of any Mathlib classical instances accidentally imported into the
  proof cone, followed by their elimination or explicit justification.
