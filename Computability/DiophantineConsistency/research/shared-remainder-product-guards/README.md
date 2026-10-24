# Six anchored remainder products, with the arithmetic body unchanged

This ordinary packet replaces six pairs of scalar guards by six product
guards rs>=0, retaining one direct nonnegative anchor pair for every shared
sum. Ten exact source ideals give r+s=a+b for each merged pair. The anchors
make that sum nonnegative; the product then forces r,s>=0 over integers.
Every removed sign is restored before any old source/Pell reasoning.

[PROOF.md](PROOF.md) proves both directions uniformly for every integer
zero of the unchanged raw body. [BOUNDARY.md](BOUNDARY.md) states the full
logical and numerical interface. The full materialized parent has1436
integer coordinates and1242 residuals, with56 guard graphs. Its body still
has1268 coordinates and1186 rows. No projected count, CSE or optimizer
result is claimed. Entire W/A/Pell tuples stay fixed; only guard witnesses
are reconstructed using the existing Legendre universality lemma.

[CERTIFICATE.json](CERTIFICATE.json) binds all ten source cuts, six signed
anchor differences and every replaced graph. [CUTS.json](CUTS.json) covers
every body/parent row, retained/removed old auxiliary and new product
auxiliary. The complete old finite and ordinary packets are content-pinned.
The stdlib-only checker imports no producer, parent checker, optimizer,
incoming code or Lean. It independently checks all source/graph bindings
and actual corruptions; finite controls are not the unbounded proof.

```sh
python -B Computability/DiophantineConsistency/research/shared-remainder-product-guards/build.py --check
python -B -O Computability/DiophantineConsistency/research/shared-remainder-product-guards/build.py --check
python -B Computability/DiophantineConsistency/research/shared-remainder-product-guards/check.py --output /tmp/shared-remainder-product-normal.json
python -B -O Computability/DiophantineConsistency/research/shared-remainder-product-guards/check.py --output /tmp/shared-remainder-product-optimized.json
```

The builder materializes only literal algebra and metadata; it executes no
engine. Normal/O receipts, independent peer review and the closed manifest
will record the final release. Current canonical pages, frozen packets,
common reports and Lean remain unchanged; no commit is made by this task.
