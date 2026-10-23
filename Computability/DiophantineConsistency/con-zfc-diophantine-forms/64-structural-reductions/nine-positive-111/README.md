# A smaller nine-positive-variable consistency equation

**Result:** exact degree **1,781,068**, **470** live binary arithmetic gates,
and nine strictly positive integer unknowns. This improves package 59's
degree 1,910,404 / 473-gate point at ProveIt commit
`beb0192cb8dc36f78c369c080f2adfbc1887a486`.

The equation is `generated/split_111_positive.json`. Its variable order is
`b,g,h,s,w,C,i,j,n`. Every other register is polynomial notation, not another
unknown. The nonnegative-coordinate companion has the same degree and
477 gates. No nine-unrestricted-integer theorem is asserted.

Read `PROOF.md` for the complete new source-layout, positivity, threshold and
degree arguments. The source is the same positive quadratic parent and
whole native tuple as package 59; the new packing has maximum coordinate
position 111 and convolution height 2010, with row 22 negated. This is a
modest verified combinatorial improvement, not a foundational breakthrough
or a claim that a globally simplest equation has been found.

The ordinary mathematical theorem, using the explicitly inherited compiler,
K215 calibration and Jones finalizer results, is formalizable in ZFC:

> The polynomial has no positive integer zero if and only if ZFC is consistent.

This does not assert either side of the equivalence. The new literal equation
does not have a new end-to-end Lean/Rocq or object-language ZFC proof file.

## Reproduction

Python 3.10+, standard library only. Run from any directory:

```sh
python3 /path/to/this/directory/build_nine.py
python3 /path/to/this/directory/materialize_fixed.py
python3 /path/to/this/directory/verify_candidate.py
```

The independent verifier checks all 22 exact target identities, all 22,544
source interactions, coherent native and derived coefficient bytes, three
universal ring identities, live circuit metrics, the leading homogeneous form,
and actual-tuple evaluator transcription. Modular evaluations are finite
implementation checks; the universal consistency equivalence rests on the
mathematical proof and named inherited results.

`native/build_coefficients.py` regenerates the four source ports from the
literal 430 machine actions and 943 tile records. That regeneration was run
and every raw payload digest matched `coefficients/BINDING.json`.

## Contents

- `PROOF.md`, `section.tex`: new mathematics and an integration-ready section.
- `data/`: literal parent, new positions and target certificate, three kernels.
- `generated/`: primary and natural DAGs plus cancellation-resolved degree DAGs.
- `coefficients/`, `fixed/`: all native and derived integer leaves, with hashes.
- `build_nine.py`, `circuit.py`: attributed adapted builder and DAG implementation.
- `materialize_fixed.py`, `verify_candidate.py`: new deterministic materializer
  and independent finite checker.
- `native/`: inherited finite coefficient generator, literal source and notices.
- `upstream/`: inherited ordinary compiler/source/finalizer proof texts.
- `SOURCE_PINS.json`: pinned repository provenance.

The new source certificate is the definition. Heuristic search is not a proof
dependency and is not required to regenerate the equation.
