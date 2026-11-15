# Pappus's centroid theorem in intuitionistic primitive recursive arithmetic

This archive develops both centroid theorems in a first-order constructive
setting:

- **surface theorem:** `S = tau * M = tau * L * r_bar`;
- **volume theorem:** `V = tau * M = tau * A * r_bar`.

Here `M` is the radial first moment and `tau = 2*pi` is itself presented by
nested regular polygons.  The primary document is
[`pappus_centroid_ipra.pdf`](pappus_centroid_ipra.pdf).

## What is proved

The report gives a complete human-readable proof for fixed
primitive-recursive presentations.  The finite core is fully explicit:

1. A meridional line segment is squeezed between inscribed and circumscribed
   regular-polygon frusta.  The gap has a primitive-recursive geometric bound,
   and the common area is `tau * ((r0+r1)/2) * length`.
2. A rectangular cell rotates to an annular cylinder, whose volume coefficient
   is exactly its radial first moment.
3. Finite list induction gives the polygonal and grid-lamina versions.
4. Explicit Cauchy and boundary-cover moduli transfer the identities to
   regular-real limits.
5. Positive lower witnesses for length or area justify the centroid quotient.

The statement is a theorem schema for each fixed primitive-recursive input
presentation.  It does not quantify over arbitrary completed real functions or
arbitrary measurable sets, which are not first-order objects of iPRA.

## Formalization status

- `lean/PappusFinite.lean` contains the finite list-level algebra over an
  arbitrary linear ordered field and has **no `sorry` declarations**.
- `lean/PappusRoadmap.lean` is an explicit formalization outline.  Its `axiom`
  declarations are named remaining obligations, not claimed proofs.
- A full object-level derivation in `PRAAx`, and its transport to `TeqAx`, is
  not yet completed in this archive.
- Lean was not installed in the artifact-building environment, so the Lean
  files were not locally kernel-checked.  They are written for the pinned
  ProveIt/Mathlib interfaces documented in `SOURCE_PROVENANCE.md`.

## Exact finite checker

Run:

```bash
python3 code/pappus_checker.py certificates/sample_certificate.json
```

The checker uses only `fractions.Fraction` and verifies the sample segment
length equations, cell shell identities, finite moments, centroids, and total
coefficients of the symbolic constant `tau`.

The checker does **not** verify represented-real convergence or the iPRA proof;
those are the Lean obligations.

## Rebuild

Requirements:

- Python 3.10 or later;
- `latexmk` and a reasonably complete pdfLaTeX installation;
- `sha256sum` and `zip` for packaging.

Commands:

```bash
make check
make pdf
make hashes
```

or:

```bash
./build.sh
```

To check the Lean files, place them in a checkout of the pinned ProveIt commit
under a source directory visible to its `ConciseIPRA` Lake library, then run
`lake env lean` on each file.  `PappusRoadmap.lean` is expected to retain its
named axioms until the corresponding phases are discharged.

## Files

- `pappus_centroid_ipra.tex`, `pappus_centroid_ipra.pdf` - report.
- `lean/PappusFinite.lean` - completed finite algebra scaffold.
- `lean/PappusRoadmap.lean` - semantic and object-theory roadmap.
- `FORMALIZATION_PLAN.md` - detailed dependency and obligation ledger.
- `code/pappus_checker.py` - exact-rational certificate checker.
- `certificates/sample_certificate.json` - worked examples.
- `verification_output.txt` - recorded successful checker run.
- `SOURCE_PROVENANCE.md` - pinned online sources and repository interfaces.
- `notes/pdf_preflight.txt`, `notes/lean_static_audit.txt` - build audits.
- `MANIFEST.txt`, `SHA256SUMS` - inventory and checksums.
