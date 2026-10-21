# Exact Rocq proof-data reductions and symmetry

New proofs were compiled with **Coq 8.18.0 / OCaml 4.14.1**, and recursively checked by `coqchk`. `verification/kernel-result.json` and the raw logs bind the result. This is not a fresh build under the repository's pinned Rocq 9.1.0 toolchain or a new full ZFC endpoint.

## Checked theorems

- `CertificateIdentity.compact_certificate_exact`: the complete compact certificate equals the original 2,240-entry certificate, by `reflexivity`.
- `CompactCertificate.unpack_pack_path`: the structural positive-integer path codec is a left inverse, for every Boolean path.
- `OffsetMirror.ocheck_mirror`: a passing certificate for the actual offset checker has a passing mirrored certificate.
- `OffsetMirror.ocheck_iff_of_forward`: a single forward check proves halting equivalence for every register file at the empty pointer.

All assumption reports are `Closed under the global context`. No axiom/admit is introduced. The generic checker and register semantics are imported unchanged.

## Reproduce

Offline certificate equality, using an installed Coq/Rocq-compatible `coqc` and matching `coqchk`:

```sh
python3 build.py --certificates-only --out /tmp/k215-cert-check
```

Full checker-symmetry check using the K230 source checkout already used by ProveIt's Rocq build:

```sh
python3 build.py --reference /path/to/k230-rocq --out /tmp/k215-mirror-check
```

Or retrieve the two exact upstream files, verified against retained SHA-256 pins:

```sh
python3 build.py --fetch-upstream --out /tmp/k215-mirror-check
```

Optional `--coqc`, `--coqchk`, and `--coqlib` arguments select a toolchain. Outputs are placed in the supplied build directory. Run proof compilers serially.

## Incorporation

Place the new `OffsetMirror.v` in the `K215F` logical namespace, and replace the second computation in `Source215.v` as illustrated by `Source215.forward-only.patch`. Update the authoritative generator/template and manifest alongside its generated output; an edit only to the generated file will be lost on regeneration. Rebuild the affected production source equivalence and final endpoint under the repository's pinned toolchain.

`CompactCertificate.v` is the compact production prototype; install its contents as `Cert215Offsets.v` in the existing `K215F` namespace. The generator is in `../proof_audit/compact_rocq_paths.py`. Its exact equality to the original permits transport through any existing checker. Keep the old certificate as an integration fixture until the normal build passes.

## Provenance

`OriginalCertificate.v`, the copied offset checker, and their hashes come from ProveIt commit `b6c7087477e51c017003bd729e712c8969733223`. The source semantics and base checker come from Elliot Glazer's K230 repository at `3142e4dd980f0be12f4abb636c4ae2528afc17eb`; exact paths/hashes are in `upstream-pins.json`. Those two upstream files are retrieved separately instead of assigning them a new blanket license. `UPSTREAM-NOTICE.md` preserves the upstream attribution and license boundaries.
