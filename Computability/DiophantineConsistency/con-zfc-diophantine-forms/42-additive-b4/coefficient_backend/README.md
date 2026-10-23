# Nonzero-code coefficient backend for Con(ZFC)

This directory is a self-contained reproducible coefficient package. It
uses the existing K215/Wang943 language and the existing four-port native
compiler interface, with two new reductions: nonzero label words and a
shorter exact-support synchronization layout.

* Base: `B = 2^683195` (previous smallest reviewed base: `2^1012115`).
* Maximum coefficient: 688,546 bits.
* Total of four minimal-width raw payloads: 342,269 bytes.
* No change to the compatible arithmetic skeleton's variable count,
  equation count, degree or gate count.

Run with Python 3, standard library only:

```
python3 build_coefficients.py
python3 audit_coefficients.py
python3 verify_equations.py
```

The builder reconstructs the literal 943 tiles from the 430 K215 actions.
The independent auditor does not import the builder; it uses the separately
pinned tile list, reconstructs the four exact integers, and checks 59,902
scalar interface identities, support intersections, carries, masks and
the new prime controller.

`PROOF.md` supplies the ordinary universal adapter proof and its dependency
boundary. `COEFFICIENT_BINDING.json` specifies exact payload hashes and
certificates. `coefficients/*.bin` are headerless minimal-width unsigned
little-endian integers; `.bin.gz` files expand exactly to them.

The ports, all replaced together, are

```
Bm1       <- beta
Kconstant <- K
MC        <- MC
MF        <- MF_source
```

`MF_source` includes the shift by `B-1`; it is not the native high mask.
Jones/Sun index constants must be recomputed if their parent quartic is
rebound. This package does not alter any low-variable compression's
previously fixed indices.

No new Lean/Rocq end-to-end theorem, proof of consistency, or global
optimality claim is made. The new tuple is a compiler backend, rather than
a new universal Diophantine-representation theorem.

## Concrete bound equations

`equations/product67_nonzero683195.json` is one degree-155 equation in 15
strictly positive unknowns, evaluated in 67 operations (39 multiplications,
28 additions/subtractions). `equations/retained16_system59_nonzero683195.json`
is a system of seven equations in 16 strictly positive unknowns, with
maximum residual degree 24, evaluated in 59 operations (33 multiplications,
26 additions/subtractions; comparisons free).

The arithmetic graphs are unchanged copies of package 36's baseline graphs.
All four coefficient ports are now concretely fixed to this package's
payloads, with exact port hashes embedded in each binding. Their original
graphs and inherited arithmetic proofs are included. The new compiler proof
transfers their established equivalence to Con(ZFC) to this tuple.

`verify_equations.py` checks literal graph equality, coefficient bindings,
degree bounds including the exact main-norm cancellation, degree attainment
by nonzero modular leading coefficients on a specified line, and liveness
of every gate and port. It writes `equations/VERIFICATION.json`.
