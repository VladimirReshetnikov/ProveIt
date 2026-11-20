# Formalization blueprint: analytic operators, integral semantics, and Rips certificates

## Status and intended endpoint

The accompanying chapter proves the mathematical assertions and specifies their finite rational witnesses. This document is a formalization plan. The displayed Lean fragments are **uncompiled interfaces**, not completed theorems. A Lean theorem about functions or `ℚ` is not by itself an object-iPRA derivation. The final arithmetic endpoints must have type `Prf PRAAx Γ φ` using the pinned ProveIt syntax and calculus.

Source pin: `b2341af5370cd8a43f72ebb2341c0d7d7395b634`.

Do not add an axiom of real completeness, a universal PR evaluator, or a new reflection rule. Supplied laws stay in the antecedent until an actual object proof discharges them.

## 1. Rational seminorms and rapid names

A convenient semantic layer uses a rational vector space with a rational-valued seminorm. The eventual code layer can use redundant codes and a proved equivalence relation. It must prove compatibility of the operations and norm with that relation.

```lean
import Mathlib

namespace QuantitativeContinuous

structure QSeminorm (V : Type) [AddCommGroup V] [Module ℚ V] where
  norm : V → ℚ
  nonneg : ∀ x, 0 ≤ norm x
  zero : norm 0 = 0
  neg : ∀ x, norm (-x) = norm x
  add : ∀ x y, norm (x + y) ≤ norm x + norm y
  smul : ∀ (a : ℚ) x, norm (a • x) = |a| * norm x

def eps (n : Nat) : ℚ := 1 / (2 : ℚ)^n

def Rapid {V : Type} [AddCommGroup V] [Module ℚ V]
    (N : QSeminorm V) (a : Nat → V) : Prop :=
  ∀ p q, p ≤ q → N.norm (a q - a p) ≤ eps p

def SameName {V : Type} [AddCommGroup V] [Module ℚ V]
    (N : QSeminorm V) (a b : Nat → V) : Prop :=
  ∀ p q, N.norm (a p - b q) ≤ eps p + eps q

structure BoundedQLinear {V W : Type}
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    (NV : QSeminorm V) (NW : QSeminorm W) where
  map : V →ₗ[ℚ] W
  bound : Nat
  bound_ok : ∀ x, NW.norm (map x) ≤ (bound : ℚ) * NV.norm x
```

The function `h M` is the least `j ≤ M+1` with `M ≤ 2^j`. Implement it by a bounded scan, or by a primitive recursion that doubles its accumulator until the bound is reached. Do not use unbounded minimization. Prove:

1. `M ≤ 2^(h M)`;
2. `h 0 = 0` and `h 1 = 0`;
3. monotonicity of `h`;
4. `(M : ℚ) * eps (n+h M) ≤ eps n`.

The semantic theorem `extend_rapid` has exact conclusion
`Rapid NW (fun n => T.map (a (n + h T.bound)))`, from `Rapid NV a`.
Its proof uses subtraction preservation of the linear map, `T.bound_ok`, the rapid inequality, and item 4. No analytic library theorem is needed.

For `extend_sameName`, replace the rapid inequality by `SameName NV a b`.

For `extend_comp`, compare source indices `p+h(MN)` and `q+h(M)+h(N)` and use the sum of their two dyadic errors. First prove the symmetric bound
`NV.norm (a i-a j) ≤ eps i+eps j` from rapidness. Cases `i≤j` and `j≤i` use decidable **natural-number** order.

For `SameName` transitivity, the intermediate index introduces a rational slack `2*eps j`. Prove a separate rational-slack-elimination lemma with an explicit index derived from the denominator of a possible positive rational gap. This is not a real-limit axiom.

For bilinear extension define `BilinearBounded` by a rational bilinear map, a natural bound `M`, and the law `norm(B x y) ≤ M*norm x*norm y`. The main finite lemma is the two-term difference estimate in the chapter. Uniform norm bounds on both name sequences provide the shift `h(M*(R+S))`. To compare constructions using different bounds, first enlarge them to a common pair and compare each old constructor to the reindexed constructor.

### Object-language bridge

Each semantic operation is replaced by a concrete PR symbol with natural-number codes. For this application the codes are signed rational vectors and refinement levels. Needed invariants are:

- denominators are positive;
- the accumulator is the exact processed numerator sum after common-denominator conversion;
- the current refinement represents the same step function;
- the processed norm difference is bounded by the processed budget sum.

The target theorem for an operator is a schema over its fixed PR implementation:

`Bound(T,M) ∧ RapidAt(a,p+hM,q+hM) → NormLe(T(aq)-T(ap),2^(-p))`.

`Bound(T,M)` is a supplied object formula or a library theorem. It is not inferred by testing finitely many vectors.

## 2. Finite probability kernels and bounded-compression pullbacks

Definitions:

- `ProbabilityVector n`: a rational vector `p : Fin n → ℚ`, with nonnegative entries and sum one.
- `Kernel p q`: rational entries `K : Fin n → Fin m → ℚ`, nonnegative, rows summing to one, and the marginal identity `q j = ∑i, p i * K i j`.
- `weightedL1 p f := ∑i, p i * |f i|`.
- `pull K f i := ∑j, K i j * f j`.
- `compose K L i k := ∑j, K i j * L j k`.

Theorems:

1. `weightedL1 p (pull K f) ≤ weightedL1 q f`;
2. `pull (compose K L) f = pull K (pull L f)`;
3. identity kernel acts as identity;
4. positivity and the constant-one vector are preserved.

Proof path: finite triangle inequality, nonnegative coefficient multiplication, interchange of two finite sums, and the marginal identity. Object proofs use nested finite folds. The invariant for sum interchange states equality of the two sums over the processed rectangle.

For a deterministic map `τ : Fin n → Fin m`, define its target mass
`massτ j := ∑ i with τ i=j, p i`. A compression certificate is
`∀j, massτ j ≤ D*q j`. It implies
`weightedL1 p (f ∘ τ) ≤ D*weightedL1 q f`.

The dyadic refinement version contains a PR table producer and proves compatibility with refinement for every demanded level. A finite table certificate at one level is insufficient for a uniform pullback theorem.

## 3. Integral formula syntax

Use an indexed syntax `Formula d`, where `d` is the number of probability coordinates:

- an atom is accompanied by its name **in the current context**;
- an exact rational connective is accompanied by coordinatewise nonnegative integer sensitivities;
- `integrate : Formula (d+1) → Formula d`;
- `pullback τ : Formula m → Formula n` only when `τ` has a certified compression bound.

The finite value of a formula is a dyadic table. Refine children to a common level before applying a connective. Integration averages over the last coordinate. Every table producer must be a fixed PR family or carry a PR clock; no evaluator for arbitrary PR function codes is assumed.

Define the sensitivity expression recursively:

- atom: its assigned error variable;
- connective: sum of child expressions times the coordinate sensitivities;
- integral: unchanged expression;
- pullback: multiply by its compression bound.

Main semantic theorem:

`L1Distance(eval φ interpretationA, eval φ interpretationB) ≤ sensitivity φ atomErrors`.

For each fixed formula, a proof by syntax induction is finite metatheoretic assembly of already proved object lemmas. A uniform compiler over syntax requires a separate correctness theorem and primitive recursive bounds on tables and intermediate arithmetic. The delivered chapter does not claim that compiler has already been completed.

### Necessary negative tests

- `diagSquares m i j := if i=j then 1 else 0` on a `2^m × 2^m` uniform table. The table has norm `2^(-m)`, but its diagonal pullback has norm one.
- `spike m` is one occupied cell in a `2^m` uniform table. Its norm is `2^(-m)`, while its maximum is one.

These show that a full first-order substitution constructor and a `sup` constructor cannot be assigned finite uniform L1 sensitivities.

### Upgrade theorem

For pointwise represented, uniformly `L`-Lipschitz functions on the `d`-cube prove

`supNorm(f-g) ≤ δ^(-d)*L1Norm(f-g) + 2*L*δ`.

Start with rational `x` and a rational inward cube of side `δ`. Prove the integrated pointwise inequality by finite Riemann sums. Use the supplied common Lipschitz modulus to pass to the integral and to arbitrary represented points. The explicit choice

`a = k + h(8*L+1); r = k+d*a+1`

turns an L1 modulus at precision `r` into a uniform modulus at precision `k`.

Do not formalize `supNorm` by assuming a new supremum exists. The stronger operational conclusion is the pointwise bound `∀x, |f x-g x| ≤ 2^(-k)`; it supplies the uniform name directly. A semantic supremum may be added later as an interpretation theorem.

## 4. Rational Rips certificates

A finite pseudometric table is sufficient; separation of zero-distance vertices is unnecessary:

```lean
structure RationalMetricTable where
  size : Nat
  dist : Fin size → Fin size → ℚ
  nonneg : ∀ i j, 0 ≤ dist i j
  self : ∀ i, dist i i = 0
  symm : ∀ i j, dist i j = dist j i
  triangle : ∀ i j k, dist i k ≤ dist i j + dist j k

def IsRipsSimplex (A : RationalMetricTable) (r : ℚ)
    (s : Finset (Fin A.size)) : Prop :=
  s.Nonempty ∧ ∀ i ∈ s, ∀ j ∈ s, A.dist i j ≤ r
```

A finite correspondence is a Boolean relation `R i j`, a nonempty-row witness, a nonempty-column witness, and the distortion inequality for every two marked entries. Select the least marked index in each row/column by bounded search.

For each simplex prove:

1. `f(s)` has diameter at most `r+η`;
2. `s ∪ (g∘f)(s)` has diameter at most `r+2η`;
3. `f(s) ∪ f'(s)` has diameter at most `r+η` for two subordinate selections.

The mixed-distance estimate in item 2 is essential; separate simpliciality alone does not establish contiguity.

### Chain coding

For the semantic layer, a chain can be a finitely supported `ZMod 2` function on finite vertex subsets. Validity at dimension `q` means every nonzero coefficient is on a `(q+1)`-element Rips simplex. The boundary of a basis simplex is the sum of its one-vertex deletions; for a one-vertex simplex it is zero. Extend linearly.

A vertex-list normalizer sorts the list, returns zero if a vertex repeats, and otherwise returns the basis vector of its set. Define a chain map on each simplex by this normalizer applied to its vertex image. Define the prism by the `q+1` mixed lists in the chapter.

Proof order:

1. boundary commutes with normalization, including duplicates;
2. `boundary ∘ boundary = 0`;
3. each simplicial map commutes with boundary;
4. for contiguous maps, `boundary(P c)+P(boundary c)=f#c+g#c`;
5. apply to the correspondence maps and their composites.

The object layer can encode chains as bit vectors indexed by sorted simplices. Symmetric difference is addition. The coefficient invariant tracks parity of all processed terms for a fixed target simplex. The canonical cancellation pairing proves the prism identity with bounded loops. Bounds include `N^(q+1)` candidate ordered tuples and at most `(q+1)*supportSize` raw prism terms.

### Main object endpoint

The final target is an implication between concrete Boolean/rational finite predicates:

`Metric A ∧ Metric B ∧ CorrDist R η ∧ Cycle q z r → boundary (prism (g∘f) id z) = map g (map f z)+z`.

No abstract quotient or barcode theorem is required for this endpoint. Homology equality is its semantic reading.

## 5. Approximate distances and nets

Use labelled finite indices as vertices. True distances between represented points form a pseudometric; do not quotient labels by equality of represented points. Given two rational symmetric tables `dtilde`, `dtilde'` and certified error bounds `η,η'` relative to the same point distances, prove the entrywise estimate
`|dtilde i j-dtilde' i j| ≤ η+η'`.

Define `Clique dtilde r` without a triangle-law requirement. Inclusion at shifted scales is a direct rational inequality for each edge. This gives literal composite inclusions. It deliberately avoids deciding whether an exact represented distance equals `r`.

For a PR finite-net selector `s : Xcore → Fin n`, use the three triangle inequalities to establish contiguity of inclusion and `j∘s` across shift `2ε`. The chain factorization is the arithmetic endpoint. The semantic rank bound is `n^(q+1)` because the finite intermediate chain group has at most that many basis elements. Proving a precise Betti number can be a later module using explicit elimination certificates.

The construction requires a certified cover and an evaluation batch for any point-name inputs. It does not supply a cover, a modulus of compactness, or a small-scale reconstruction theorem from bare classical compactness.

## 6. Completion gates

A claim becomes **kernel checked in the object theory** only after:

1. the PR code and positive-denominator rational lemmas are implemented;
2. the finite kernel laws have actual `Prf PRAAx` proofs;
3. name/cover/refinement/regularity hypotheses are explicit object formulas;
4. fixed precision substitutions are inserted through the existing syntax API;
5. each analytic consequence is assembled from these derivations;
6. the resulting declarations compile at the pinned toolchain without `sorry` or extra axioms.

The present files provide the definitions, human proofs, and explicit targets for those gates. They do not assert that unimplemented gates are complete.
