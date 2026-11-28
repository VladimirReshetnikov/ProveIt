# Checked Lean support for spectral trace interpolation

These two files contain eight proved declarations supporting the proposed
trace-recovery simplification. They are independent of the ProveIt GRH modules.

## Reproduce with Lake

Install the Lean toolchain manager `elan`, then run from this directory:

```sh
lake exe cache get
lake build
```

The supplied `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin
Lean **4.35.0**, Mathlib commit
**56a005855ea17e0b0958f73ec801ae140b0a1679**, and Mathlib's transitive
dependencies. Keep the manifest when reproducing this check; an update of
dependencies is not needed. The first command needs network access to obtain
the packages and Mathlib's compiled cache. Lake can compile missing cached
modules from their pinned sources.

The package configuration is supplied for portable reproduction. The authoring
session **did not run `lake build` on this delivered package**. Instead, both
delivered `.lean` files were checked with the exact Lean compiler against the
same pinned Mathlib checkout, using a local dependency overlay. The first file
was compiled afresh before checking the second. No compiled `.olean` files or
dependency caches are included in this archive.

The actual commands, versions, and working directory are recorded in
[`../results/lean/reproduction-environment.txt`](../results/lean/reproduction-environment.txt).
Compiler output is in
[`../results/lean/SpectralTraceCore.check.log`](../results/lean/SpectralTraceCore.check.log)
and
[`../results/lean/SpectralTraceSpectrum.check.log`](../results/lean/SpectralTraceSpectrum.check.log).
The source checksums and verification scope are in
[`../results/lean/spectral_lean_verification.json`](../results/lean/spectral_lean_verification.json).

## What is proved here

`SpectralTraceCore.lean` proves five statements in namespace
`SpectralTraceCore`:

1. `exists_interpolant_zero_constant`: for a finite set of nonzero field
   elements, interpolate arbitrary values with a polynomial having zero
   constant coefficient and degree at most the number of nodes.
2. `linear_aeval_eq_of_positive_moments`: agreement of linear functionals on
   positive powers through degree `N` gives agreement on every polynomial of
   degree at most `N` with zero constant coefficient.
3. `trace_mul_aeval_eq_of_positive_moments`: specialize the preceding result
   to the functional `X ↦ trace (A * X)` on endomorphisms.
4. `rank_from_determinant_norm`: extract `r` logarithmically from
   `u = d^n * (1+c)^r`, where `d,c > 0`.
5. `trace_projector_eq_of_polynomial_certificates`: combine the transport
   theorem with two **explicitly assumed** polynomial trace certificates.

`SpectralTraceSpectrum.lean` proves three further statements:

6. `zero_not_mem_charpoly_roots_of_det_ne_zero`: an endomorphism with
   nonzero determinant has no zero characteristic root.
7. `card_distinct_charpoly_roots_le`: the number of distinct characteristic
   roots is at most the dimension.
8. `exists_common_root_interpolant`: for two endomorphisms with nonzero
   determinants, interpolate arbitrary values at all their characteristic
   roots with one zero-constant polynomial of degree at most the sum of their
   dimensions. Over the complex numbers these roots are precisely the
   eigenvalues.

Both source files compile without warnings. The printed axiom reports for all
six main endpoints contain only `propext`, `Classical.choice`, and `Quot.sound`.
There is no `sorry`, `admit`, `sorryAx`, or custom axiom in either file.

## Exact boundary of the formal verification

The report proves mathematically the following spectral trace identity. If

```text
T * adjoint T = d * (1 + c * e),
e * e = e,  d > 0,  c > 0,
```

and `A` commutes with both `T` and `adjoint T`, choose a polynomial `p` whose
value at every eigenvalue `z` of `T` is

```text
log (norm z ^ 2 / d) / log (1 + c).
```

Then `trace (A * e) = trace (A * aeval T p)`. **That spectral identity is not
formalized in these files.** In the fifth theorem it appears as the explicit
hypothesis `hcertificate`, with a second hypothesis `hcertificate'` for the
other space. These hypotheses must be proved before applying the theorem to
the source line relation; they are not hidden axioms and are not discharged by
this package.

The full theorem's reduction to a finite list of trace moments is therefore
supported by checked interpolation and transport code, while the central
spectral argument remains a complete human-readable proof in the report.
Neither the adelic source adapters nor the Hua/Schur-complement proposal is
formalized here. Successful checking of these files is not a rebuild, audit,
or replacement proof of the full GRH project.
