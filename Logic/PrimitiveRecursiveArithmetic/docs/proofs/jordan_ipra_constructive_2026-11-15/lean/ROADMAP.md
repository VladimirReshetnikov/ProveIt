# Lean formalization roadmap and status

## What is present

`FiniteKernel.lean` supplies proposed executable rational definitions.
`NativeTransfer.lean` shows the exact existing ConciseIPRA bridge to use after
the arithmetic derivation has been constructed. Both are **uncompiled source
scaffolds**: Lean was not installed in the delivery environment. Neither file
claims a completed Jordan theorem, and neither uses `sorry` or declares an
axiom. The Python finite kernel was executed; its output is separate evidence,
not a Lean proof.

The repository was inspected at commit
`620f5e3b959c3a4284060ada5efb651812612319`. Its toolchain is
`leanprover/lean4:v4.32.0`; its Mathlib requirement is `v4.32.0`.

## Two distinct targets

1. **Semantic correctness.** Prove the rational algorithms correct in Lean,
   using natural numbers, integers, rational pairs, and finite lists.
2. **Proof-theoretic correctness.** Construct actual derivations in
   `LeanProofs.ConciseIPRA.PRAAx` of the arithmetical versions. Ordinary Lean
   correctness of an algorithm does not automatically establish this target.

The main article gives a human proof of the bounds and of why its induction
invariants can be made quantifier free. The tasks below make the implementation
route explicit rather than using Lean's classical Jordan theorem.

The main proof needs **crossing parity only**. Integer winding numbers in the
reference code are an optional stronger exact-arithmetic helper. All stated
index obligations can be reduced modulo two, removing the orientation and
signed-degree bookkeeping from the trusted proof.

## Modules and obligations, in dependency order

| Proposed module | Objects and precise obligations | Human proof component |
| --- | --- | --- |
| `Coding` | Signed integers and rational pairs with positive denominator, bounded lists, arrays, finite minimum, finite sum, bounded search; PR terms and defining-equation derivations | Arithmetic coding and bounds |
| `RationalGeometry` | Determinant signs, interval overlap, point/segment distance bounds, finite boxes; division is only by a certified positive integer | Exact rational geometry |
| `Parity` | Half-open ray-crossing count modulo two; concatenation and subdivision; triangle boundary contributes parity zero when the probe lies outside the triangle | Elementary parity lemma |
| `ParityHomotopy` | Equal parities under a finite strip of triangles avoiding a probe; parity constancy on a path with certified clearance | Triangle replacement and finite telescoping |
| `CircleWalk` | Shorter cyclic walks; unsigned edge-usage counts modulo two; the closed-walk condition makes all edge counts equal to one bit m | Parity factorization lemma |
| `Honeycomb` | Six rational vertices, neighbors, edge agreement, exactly three cells at an interior vertex; dual links cross only their own shared edge | Rational tiling lemma |
| `FiniteGraph` | V-round reachability; parent extraction with length at most V; one-in/one-out boundary graph splits into simple cycles in at most E steps | Bounded flood fill and boundary traversal |
| `Connection` | If endpoints have equal parity, the target is reached. Otherwise the selected boundary cycle changes parity by one between the endpoints; factorization transfers this to the original curve | Main connection dichotomy |
| `BothSides` | Bounded local construction of off-curve witnesses with opposite parities near every named curve point | Boundary/nonemptiness argument |
| `Names` | Rational fast names and fixed PR evaluators; finite sampling and distance certificates from supplied moduli | Constructive presentation |
| `JordanSchema` | Classification, paths with clearance, witnesses near every curve point, bounded interior/unbounded exterior, approximate crossing at each requested precision | Main theorem |
| `ObjectDerivations` | Encode each finite invariant as a characteristic-function equation, prove it with `PRA.qfInd`, and assemble the closed theorem for each fixed PR presentation | iPRA audit |
| `NativeJordan` | Apply `pra_iff_native` to the completed object-level derivation | Existing repository bridge |

## Parity obligations without analytic winding numbers

The executable helper sums signed intersections of polygon edges with the
positive horizontal ray from the query point; the main proof uses its value
modulo two and needs no orientation. Use half-open y
intervals to make vertex hits deterministic. Prove the triangle identity first
for rational probes and rational triangles. The finite case split is over the
relative ordering of three y coordinates and determinant signs. Degenerate
triangles follow by collinear subdivision/cancellation. Then derive:

* subdivision and cancellation of an edge with its reverse;
* insertion/deletion of a vertex across a triangle avoiding the probe;
* invariance under a rectangular mesh of avoiding triangles;
* constancy along a probe path by applying the same lemma to relative vectors.

For the parity development, count each sample edge's usage modulo two,
ignoring direction. The closed-walk condition says the two incident edge counts
at each cyclic vertex agree modulo two. Thus all edge counts equal one bit m,
and the polygon parity equals m times the original sampled-curve parity.
The separating boundary changes parity by one between the endpoint cells;
hence m=1 and the two original curve parities differ. This is sufficient for
the connection theorem and avoids proving the stronger integer factorization.

The optional stronger signed development counts oriented edge traversals
instead. Conservation then gives an integer degree and an integer-index
factorization. It is tested in Python but is unnecessary for the theorem.

## Finite invariants to encode as equations

All of the following are predicates on bounded arrays. Replace each with an
explicit 0/1-valued characteristic function before applying induction.

* Every processed ray crossing contributes a bit; the parity accumulator is
  the exclusive-or of the processed prefix.
* The current flood set contains the root and is contained in the patch.
* Every discovered vertex has a parent with strictly smaller discovery rank;
  its parent link has the recorded clearance certificate.
* After k rounds, every safe-link path of at most k links from the root ends in the set.
* Every internal separating vertex has exactly one entering and one leaving
  directed edge; the orbit traversal has no repetition before its return.
* A finite triangular strip has a telescoping boundary parity; internal edges
  occur twice and cancel modulo two.
* At every cyclic sample vertex, the two incident edge-usage parities agree.

Induction is on a natural counter bounded by the already constructed array
length. A bounded quantifier is a finite Boolean fold, not a new unbounded
induction schema. Totality bounds must be proved for the concrete functions;
one must not infer that arbitrary terminating programs are PR.

## The presentation schema

Do not quantify over a universal evaluator for all PR programs. Fix a finite
tuple of PR symbols for the curve approximator, its forward modulus, its
inverse/separation modulus, and the input point approximators. Each theorem
instance is an ordinary first-order arithmetic sentence with number parameters.
Global regularity premises are universal arithmetic formulas. A particular
output uses only a bounded finite set of their instances. Object-level
induction remains on decidable finite invariants, with the global premises
kept as assumptions in the proof context.

If an oracle-relative theorem is useful while developing the semantic layer,
label it as such. It becomes an iPRA theorem schema only after fixing PR
evaluators and supplying object-level derivations from the stated arithmetic
premises. Proving the premises themselves is additionally required only for an
unconditional concrete instance.

## Inspected repository API

`ConciseIPRA/PR.lean` defines:

* `PR`: `zero`, `succ`, `proj`, `comp`, `prec`;
* `PTm`, the syntax of arithmetic terms;
* `PRAAx`, the defining equations, successor axioms, and QF induction;
* `PRA.qfInd`, the derived proof constructor for QF induction.

`ConciseIPRA/NativeBiInterpretation.lean` defines:

* `NFm.ofPRA` and `NFm.toPRA`;
* `pra_iff_native` and `native_iff_pra`;
* the two provable round trips and `native_inconsistent_iff`.

These facts license reuse of the arithmetic proof system and its native
translation. They do not contain a Jordan theorem or automatically translate
an arbitrary Mathlib proof into iPRA.

## Suggested verification commands after integration

Place the modules in a fresh `JordanIPRA` Lean library in the pinned ProveIt
checkout and declare its `srcDir` in that checkout's Lake configuration. Run
`lake env lean` on each module and `lake build JordanIPRA`. Add `#print axioms`
for the final semantic theorem and for each object-level proof-construction
theorem. Review imports as well as reported axioms: classical reasoning hidden
in a general real-analysis theorem is not justified merely because a source
file contains no visible `classical` command.

The completion gate is an object-level value of the stated `Prf PRAAx ...`
type, together with the explicit PR witness terms and their correctness
derivations. The present package does not claim to have reached that gate.
