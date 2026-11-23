# Lean material and its exact status

**The new Lean files in this archive were not compiled.** A Lean or Lake executable
was not available in the execution environment. The files are a concrete
formalization outline, not a completed verification claim. No file uses `sorry`,
`admit`, an unproved `axiom`, or a claimed new soundness principle.

## Files

- `ObjectCertificates.lean` contains 24 candidate **closed object-iPRA derivations**.
  Their theorem types are `([] : List (Fm PTm 0)) ⊢[PRAAx] sentence`, using the
  actual ProveIt API. They are stronger in form than ordinary Lean theorems about
  real or rational numbers, but must still pass compilation before being called
  kernel checked. Their formulas and proof scripts were inspected manually.
- `certificate_index.json` lists each endpoint, its meaning, and its arity.
- `ExactCodes.lean` specifies signed integers, positive-denominator rational codes,
  exact rational operations, point/line/plane/conic records, a line-intersection
  construction, a dyadic square-root index, and metatheoretic fixed-name contracts.
  These data definitions do not themselves prove their translation into iPRA.
- `AnalyticPrograms.lean` supplies sparse polynomial/exponent-list evaluation,
  formal partial derivatives, the exact coefficient bounds H/B/L, finite
  trigonometric sums and their precision schedules, fixed-polynomial bisection,
  and a rational dyadic chord-sum observer for polynomial arc length. Its
  functions are explicit definitions without asserted correctness theorems.
- `BridgeSpec.lean` gives the object-language rational-term and fixed-PR-family
  interfaces. `RationalBridgeObligations` and `FiniteObservationTarget` have **no
  supplied instances**. They make the remaining work explicit; they do not assume
  the missing conclusions as axioms.
- `generate_certificates.py` reproduces the first file and its index. Generating
  source is not typechecking it.
- `consulted_sources.json` records the exact repository paths and blob hashes
  inspected when writing the outline. Source snippets in the report refer to the
  same pinned revision.
- `check_in_proveit.sh` is a future build gate. It was **not run** here because Lean
  was absent. It checks the repository revision before building and records the
  printed axiom dependencies of the 24 candidate endpoints.

## Reproducible target

Repository: `VladimirReshetnikov/ProveIt`.

Commit: `bbb85238dac533fc4b7b84a750cca864fe35fed5`.

Lean toolchain: `leanprover/lean4:v4.32.0`.

Mathlib revision: `81a5d257c8e410db227a6665ed08f64fea08e997`.

These dependencies are not copied into the archive. Use an existing checkout of
the pinned ProveIt revision with its Lake manifest and dependencies installed.
The four new Lean files have no dependencies on each other, so each can be compiled
directly through the ProveIt Lake environment.

```
bash /absolute/path/to/packet/lean/check_in_proveit.sh /absolute/path/to/ProveIt
```

The script requires the pinned revision. If adapting the packet to a later
revision, review the API differences first and record the actual new revision;
do not silently treat an untested later API as identical.

## Why `ipra_ring` is relevant

The repository encodes an integer term as `ZT n`, a pair of natural-number terms.
The object-language equality of `(p,n)` and `(p',n')` is `p+n' = p'+n`.
`Core/Integers.lean` evaluates such terms in the ring of differences of the
quotient of terms by **iPRA derivability under the current context**. Its theorem
`ZT.derive` turns equality in this quotient ring back into a `Prf PRAAx` object.
`Core/Tactic.lean` packages this into `ipra_ring`; it does not add arbitrary
semantic truths as axioms. `closeUniv` binds the natural-number variables.

Consequently the desired endpoint is a proof in the stated weak theory even
though Lean and Mathlib are used in the metatheory to construct the proof. A
separate call to Mathlib's `ring` on rational or real numbers would not establish
that endpoint. The new files follow the existing repository design.

## Remaining formalization stages

1. Typecheck the 24 polynomial certificates and inspect every `#print axioms`
   result. No unexpected axiom such as `sorryAx` may remain.
2. Connect the report's triples `(p,n,d)` with the repository's canonical rational
   encoding. Prove positive denominators, equality invariance, exact order
   comparison, and guarded inversion. Do not replace a missing positive or
   apartness guard by unrestricted choice.
3. Transport each polynomial certificate to rational coordinates by multiplying
   by an explicitly positive common denominator. Use the existing integer-order
   and cancellation libraries for inequalities and implications.
4. Compile every finite rational case distinction into a decidable test. The
   invariant for classification must include the explicit affine inverse and the
   resulting normal-form equation, not only a conic label.
5. Reuse the repository's dyadic-square-root bracket derivation. Prove the
   finite-observation input/output error bounds stated in the report, with the
   exact precision schedule and denominator gaps.
6. For a fixed represented-real family, compile its named PR programs and its
   finite list of observation conditions. Quantify only over number parameters,
   certificate bounds, and requested precision in the final iPRA formula. The
   higher-order family notation in `ExactCodes.lean` is metalanguage.
   `NameNonnegative` and `GapContract` match the report's all-precision
   contracts. The finite `ApartWitness`, together with `NameCondition`, implies
   `GapContract` by the rational reverse triangle inequality; this implication
   remains to be entered as a Lean proof.
7. Add each completed endpoint to the repository's axiom audit. Only after this
   gate should the report's status be changed from a human proof plus outline to
   a verified formalization for that endpoint.

## Scope of the 24 certificates

They cover the polynomial content of Gram/Lagrange and parallelogram identities,
the cosine law, Cramer construction and recovery, scaled rotations, determinant
area transport, reflection and projection, circle and sphere parametrization,
quadratic completion, the parabola focus relation, quadratic restriction to a
line, discriminant transport, cross products, skew-line normal separation,
weighted variance, radical axes, and quadratic midpoint identities.

The certificates do not by themselves formalize root existence, square-root
continuity, full conic classification, irrational coordinates, or the analytic
tangent theorem. Those use the named bridge stages above and the report's
finite constructive arguments.
