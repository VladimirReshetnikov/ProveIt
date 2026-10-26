# Five further Lean proof simplifications

Prepared for Vladimir Reshetnikov, 26 October 2026.

**Source revision:** `9d9d1123b39927d30363f1dcd53c23f0575c30ee` in
<https://github.com/VladimirReshetnikov/ProveIt>.

Read `report.pdf` or `report.tex` for the complete analysis, proofs, novelty
comparisons, and limitations. This packet treats all previous proposals in the
36 placed packets and five incoming ZIPs as baseline infrastructure.

## Results

1. Normalize the raw binary-rotation exponent modulo the complete bit window.
   The exact output function is unchanged even for unbounded input digits.
2. Obtain nonwrapping from two strict summand bounds below the same radix window.
   The two units of integer slack include the radix-two endpoint.
3. Simplify internal division uniqueness by cancelling the common quotient term,
   retaining only one positive additive gap.
4. Derive zero-test soundness from the product and reconstruction rows; its
   literal three-row certificate stays in the production statement.
5. Expose the fixed affine controller coefficient to linear arithmetic for
   injectivity and exclusion of the optional position.

The four proposed patch files affect six theorem bodies in five production
modules. Their complete-file counts decrease from 783 to 763 physical lines,
including the one additional zero-test import. The optional general lemmas in
the research files are not added by those patches and are not hidden overhead.

## Validation scope

Five standalone Lean files, including thirteen named theorem declarations,
compile under Lean 4.32.0 and the repository-pinned Mathlib revision
`81a5d257c8e410db227a6665ed08f64fea08e997`. The compiler logs and axiom output are
in `evidence/logs/`; final results are in `evidence/validation.json`.

These are checked mathematical cores and exact-source integration candidates.
The complete production modules and downstream clients were not rebuilt.
The patches therefore require the repository's ordinary focused integration
checks before their textual reduction can be called an integrated reduction.
No build-time improvement is claimed.

## Reproduce the independent Lean checks

With the pinned Lean toolchain available:

```sh
lake update
lake exe cache get
sh scripts/check_lean.sh
```

The Lake configuration pins the Mathlib commit. The prototypes import only
Mathlib and Lean core modules, so these checks do not need the ProveIt dependency
tree. Rotation and controller definitions are copied into isolated namespaces;
the internal arithmetic proofs use abstract carriers and explicit hypotheses.

## Review and integrate the proposed patches

First use a ProveIt checkout at the pinned revision:

```sh
python3 scripts/check_sources.py /path/to/ProveIt
```

Inspect each patch. From that checkout, check the patches without applying them:

```sh
git apply --check /path/to/this-packet/patches/rotation-rephase.patch
git apply --check /path/to/this-packet/patches/no-wrap-capacity.patch
git apply --check /path/to/this-packet/patches/logic-proof-refinements.patch
git apply --check /path/to/this-packet/patches/affine-positions.patch
```

The rotation proof retains its public Boolean premise, which becomes unused.
The zero-test patch adds `ObjectNaturalOrderedSemiring` to expose the already
existing cancellation instance. An earlier proposal may already make that
import redundant; the measurement here conservatively charges it.

Suggested integration order: affine controller, rotation, capacity, division,
then zero-test. Rebuild each affected module and its direct consumers. Preserve
the literal certificate rows and production data definitions.

## Rebuild the PDF

```sh
sh scripts/build_pdf.sh
```

This uses `latexmk` and standard TeX Live packages. `report.pdf` was compiled from
the included `report.tex` and visually inspected.

## Evidence

- `source_manifest.json`: exact target source hashes and repository pin.
- `novelty-audit.json`: census counts, audit method, and limitations.
- `novelty-matrix.csv`: five proposals versus their closest earlier mechanisms.
- `novelty-notes.md`: packet-by-packet taxonomy and candidate judgments.
- `exclusion-corpus-manifest.json`: hashed inventory including ZIP text members.
- Per-patch metrics: complete source line counts and available byte hashes.
- `patch-validation.json`: dry-run patch applicability and preserved headers.
- `validation.json`, `logs/`: independent compiler evidence.
- `SHA256SUMS`: checksums of delivered files, excluding the checksum file itself.

Corpus novelty is relative to the pinned review, not a claim of mathematical
originality or a proof that no differently worded equivalent proposal exists.
