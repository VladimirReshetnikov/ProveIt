# Repeated named binding and vacuous opening

[ModelCodedBinderAbsorption.lean](Lean/ZFCinPA/ModelCodedBinderAbsorption.lean)
proves that binding the same free label twice leaves the first bound body
unchanged. The depth, label, term and formula codes range over every element
of an arbitrary model of IΣ₁. Internal Π₁ structural induction carries the
chosen label through both quantifiers; no finite-support or freshness premise
is used.

A second induction proves that substitution into a nonexistent outer bound
slot fixes a formula. In particular, opening a unary view of a formula equals
shifting its free parameters. Together these laws supply the vacuity step for
the intended decoded `rho6` proof. This module does not yet prove that row or
the PA consistency equivalence.

The first proof run passed seven named axiom probes and nine callers, with
only `propext`, `Classical.choice`, and `Quot.sound`, and no warnings. The
[original verification](results/model-coded-binder-absorption-verification.json)
is preserved byte for byte. The
[publication record](results/model-coded-binder-absorption-publication.json)
contains the two earlier unbuilt preparations, exact snapshots, maintained
preflight, and four guard rejections. Placement caused zero proof builds.

[check_model_coded_binder_absorption.py](check_model_coded_binder_absorption.py)
reuses the checked BindOne closure: ten project modules, six external source
and object boundaries, and the actual Omega provider. Its default maintained
paths passed `--prepare-only`; a complete matching dependency cache is needed
to rerun the fresh source and audit checks. It does not build dependencies.
