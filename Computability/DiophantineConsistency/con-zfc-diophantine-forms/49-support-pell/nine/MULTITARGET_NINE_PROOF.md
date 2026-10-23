# Current nine-variable proof

The active proof for the support-aware instance is
[`../SPARSE_PACKING_PROOF.md`](../SPARSE_PACKING_PROOF.md), together with
Sections 2–3 of `../report.pdf` and the exact circuit/data certificates.

Its primary positive circuit has degree **32,568,568** and **652** live
operations. The labels isolate 71 supported pairs among all 528 pairs;
they deliberately do not form a full Sidon set.

The unchanged historical package-45 proof is preserved only as provenance
at `../upstream/MULTITARGET_NINE_PROOF_PACKAGE45.md`. Its earlier numerical
claims and full-Sidon hypothesis are not definitions of the present instance.

Run `python3 ../verify.py` from this directory, or the compatibility entry
point `python3 verify_multitarget_nine.py`. The complete archive check is
`python3 ../verify_all.py`.
