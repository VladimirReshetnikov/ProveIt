# Sparse equations for singular moduli and the sign of weighted prime sums

Read **report.pdf** for the complete proofs, dependency statements and research questions. The top-level LaTeX file is **report.tex**. The companion TeX files are its sections.

## Reproduce

Run the following from the unpacked directory using Python 3.9 or newer with its standard library. Keep assertions enabled.

```sh
python3 reproduce.py
pdflatex -halt-on-error report.tex
pdflatex -halt-on-error report.tex
```

The Python runner certifies the 79 class polynomials, all 442,904 discriminants in the finite ranges for the four-term theorem, the degree-1000 exclusion for the additional five-term problem at −131, and the finite calculations for the analytic results. The detailed discriminant counts and disk witnesses are in `checks/global_sieve.txt` and `checks/disks.csv`. The latter gives positive absolute discriminants, and `class_polynomials.json` lists integer coefficients from constant to leading. All arithmetic relevant to a certificate is integer, rational or outward-rounded interval arithmetic.

The earlier 79-row list is from `grh_cm_prime_applications.zip` in ProveIt, revision c59bde1a0f52eee7a7a8dc6b326072f9b71f76a6. Its archive SHA-256 is 1ad1eb3b15a62ca4d04d0107fc151bec4681543baf69f612a786db3146dde01d. Its `checks/four_term_candidates.tsv` SHA-256 is 12fcd5a92cc357ae8b4ef187b4950bf7748bf8a3d7febf8457727a1729bc7023. We matched every discriminant and degree. The standalone global proof uses just 12 of these rows.

## Upstream

The Lean source snapshot is lsernau/grh-lean at 72fead102f663d5c7a407964a13dc0cf9d977207. To compare a separately obtained checkout, run `python3 checks/upstream_identity.py /path/to/grh-lean`. It matches Git blob IDs for the declarations, the proof guide, the pinned dependencies, and the inspected parts of the reduction. These identity checks are distinct from a Lean kernel replay. The manuscript documents the upstream machine-check record. The new arguments are paper proofs.

The SHA256SUMS file covers the deliverable files other than itself.
