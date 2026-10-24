# Round10: commutative C222 proof certificates

## Recommended component

- `section.tex`: report-ready proofs and limitation statement.
- `COMMUTATIVE_CERTIFICATES.md`: full abstract flow theorem.
- `AFFINE_PRODUCT_CERTIFICATES.md`: affine coprime weights, accumulator,
  global constructor, and separate-scale warning.
- `horn_shared_source.json`: byte-copy of the authored alternative source
  at the moment of integration, not an upstream executable.
- `affine_shared_step.json`: exact23-witness degree50 local polynomial.
- `SharedAffineProductEquation.lean`: fully specified UNCOMPILED global
  constructor proposal. Final ordinary polynomial is not materialized,
  its total variables/degree/circuit size are not reported as a record.

The source is independent of K215 simulation and Jones finalization.
It retains the calibrated numerical C222 calculus and the existing direct
Diophantine closure constructors. There are TWO separate bounded-forall
blocks. The common multiple, beta sequence scale, and compiler internal
scales are distinct; no circular identification is allowed.

## Reproduce

Run the authored scripts from this directory or by their full paths:

    python check_flow.py
    python check_affine_products.py
    python build_shared_affine_step.py
    python emit_shared_affine_constructor.py
    python check_shared_affine_step.py

The 480 modular shared-local fixtures do not assert the global common-
multiple condition; they test the local polynomial only. Exact standalone
flow/product tests cover that arithmetic lemma separately. No bounded
regression is advertised as a proof of the global theorem.

## Provisional baseline files

`build_horn_rule.py`, `flatten_horn_rule.py`, `build_affine_step.py`, and
`emit_affine_constructor.py` provide a straightforward97-local-witness
quartic baseline. The `horn_rule*` and `affine_step_quartic.json` artifacts
are intermediate comparisons, not the preferred23-witness source.
`AffineProductEquation.lean` is the corresponding uncompiled baseline.
Its checks are `check_horn.py` and `check_affine_step.py`.

## Provenance and remaining work

The local numerical coding/axioms are inherited from the authored round9
source, whose repository API/calibration pin is
beb0192cb8dc36f78c369c080f2adfbc1887a486. Branch sharing and independent
wire elimination are supplied by this round's alternative component.
Their semantic verification is required alongside this directory.
The new abstract flow theorem and affine-factor theorem are mathematical
proofs, not Lean/Rocq certificates. Next: elaborate both the local source
bridge and the closed constructor in the repository, materialize its
ordinary polynomial, and then measure it against the established frontier.
