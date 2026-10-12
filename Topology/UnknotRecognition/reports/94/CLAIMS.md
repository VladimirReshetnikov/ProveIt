# Claim ledger

## Proved here and implemented

- Validating supplied interval covers and matchings, orienting them and computing
  all critical-cell counts has polynomial encoded cost.
- Fixed-slope affine rank synthesis is exactly a difference-constraint system.
- Signed floor sums and residue-threshold counts are exact on binary intervals.
- Synchronized modular rank offsets are found exactly in polynomial encoded time.
  The matching, modulus, scale, multipliers and phases are supplied, not discovered
  by a complete general procedure.
- Independent rank replay calls neither synthesis nor the offset solver.
- Modular paths and their products with small simplicial complexes have the proved
  relative and, for the specified base matching, point-collapse certificates.
- Coordinate reflection transports the certificates exactly.

## Proved statements with narrower implementation status

- Acyclic matching with a critical subcomplex gives a collapse: written proof,
  classical discrete Morse ingredient, checked by independent finite oracles.
- Authenticated PL 3-manifold plus a one-critical-vertex certificate gives a PL ball:
  classical topological implication. Source authentication implemented only for
  the controlled product class, not native normal-cut packets.
- Exponential contiguous-affine lower bound in fixed source coordinates: proof for
  every possible affine rank, not merely a finite search. Arithmetic-progression
  refinement or a different indexing is outside this lower bound.
- Component-local rank composition: proved, not implemented.
- Quasi-polynomial catalogue and hierarchy accounting: conditional on all stated
  coverage, encoding, operation-cost and depth hypotheses.

## Evidence

18 tests and 90,121 counted cases pass; see `results/validation.json`. Controlled
paired timing queries are in `results/benchmark.json`, including regressions and
A/A controls. They compare two queries on an already supplied interval matching.
They are not end-to-end knot-recognition timings or evidence of hard-knot speedups.

## Not established or claimed

General quasi-polynomial unknot recognition; native regularization/export; pattern
transport under arbitrary collapse; a complete matching/template search; production
integration; native source or full-repository test execution; formal Lean/Rocq
verification; exhaustive literature priority.

No existing ProveIt theorem is asserted false. The report identifies unsafe
inferences to avoid at a future interface, and recognizes that source parallelity
and the bounded inherited core are already present upstream.
