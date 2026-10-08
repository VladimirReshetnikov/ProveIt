# Affine Families and Inherited Structure in Unknot Recognition

Research continuation for Vladimir Reshetnikov / ProveIt, 8 October 2026.

**Read the article:** `article/unknot_affine_families.pdf`  
**Edit and rebuild:** `article/unknot_affine_families.tex` and its `sections/`, `tables/`, and `figures/` dependencies.

## Research outcome

This continuation supplies three exact improvements and a detailed account of what still separates them from a general quasi-polynomial recognizer.

1. **Optimize a whole affine family of cyclic monodromies.** For `Az=b (mod m)` and `h=c+Hz`, the minimum component count is the gcd of the offset and generator entries of the feasible holonomy coset, together with `m`. A deterministic algorithm attains it using modular arithmetic and gcd saturation, without factoring the modulus or enumerating parameter assignments. The variable dimensions are explicitly charged in the bit-cost model. Independent primal/dual identities certify optimality, and a separating modular row certifies infeasibility.
2. **Extract actual normal-coordinate gluing data.** The implementation converts admissible seven-coordinate normal vectors and tetrahedral face pairings into signed interval bands, prism-gap identifications, and local residual-cell contacts. There are at most five surface bands per paired face, at most two exceptional prism-to-residue contacts per paired face, and at most six local residual cells per tetrahedron. Coordinate multiplicities are handled in binary.
3. **Reuse full scalar endomorphism algebras.** After a verified scalar split, child algebras are transported parent corners. Canonicalization preserves the existing deterministic candidate policy. A generator with minimal-polynomial degree equal to the complete commutant dimension can certify scalar locality and permit inheritance through one generator.

The article also proves that simultaneous designated-boundary connectedness is NP-complete already for affine three-sheeted cyclic covers of planar surfaces. This carefully separates the polynomial global component query from a more expressive peripheral query. A counting identity and the inclusion of totient computation as a special case of exact connected-assignment counting provide another boundary.

**No general quasi-polynomial unknot-recognition bound is proved.** A sound bridge from actual normal-cut geometry to a complete family representation, global state-size bounds, and hierarchy reset accounting remain open. Scalar locality is not a knot verdict. The normal extractor prepares AHT interval-orbit input; it does not implement the unrestricted orbit algorithm or a complete compressed cut manifold.

## Main evidence

- **790 integrated tests passed**, using the distributed source tree. The untouched baseline had one reproduced worker-communication failure; its correction is copied and attributed from the earlier projectors archive.
- **63,886 arithmetic comparison cases**, with independent enumeration of original variables, plus malformed-certificate, empty-dimension, cancellation, and large-JSON checks.
- **120 surface families / 1,337 original assignments**, with literal patch–sheet orbits independent of the compiled spanning-tree calculation.
- **1,537 rational geometric cases**, checking 9,771 disc and 4,850 prism identifications.
- **807 Regina inputs / 1,537 component records**, comparing complete normal-coordinate multisets and topology; these include nonorientable and closed components.
- Paired scalar measurements use **seven randomized rounds and A/A controls**. Arithmetic and normal extraction measurements have their separate timing contracts documented in the article and result files.

Selected measurements:

| Case | Result |
|---|---|
| `m=6^65536`, `h=2+z` | 169,409-bit modulus; exact minimum one; 17 saturation gcds; 0.191 s recorded median including arithmetic certificate generation/check |
| 128-tetrahedron Fibonacci meridian | About 2.79 × 10^27 discs represented by 764 surface bands, 754 prism bands, and 512 local residual cells |
| 16 attached copies | Commutant equations 2,990 → 512 and solves 15 → 1; paired speedup 1.468× |
| Dense two-field degrees 8 / 10 / 12 | Candidate counts 46 / 52 / 58 → 2; one-generator paired speedups 2.165 / 2.312 / 2.229× |
| Six natural knot scans | Inheritance ratios 0.961–1.022×; no convincing wall-time speedup, despite fewer commutant solves for Conway and Kinoshita–Terasaka |

General inheritance slows the smallest attached-copy case and the displayed two-field cases when used alone. Larger controlled cases raise default size or variable caps, as marked in the article. Absolute timings come from a shared runtime and are descriptive, not machine-independent predictions.

## Archive map

| Path | Purpose |
|---|---|
| `article/` | Complete TeX article, PDF, generated tables, vector figures, and Makefile |
| `source/Topology/UnknotRecognition/fast/` | Integrated implementation, tests, and fixtures |
| `source/Topology/UnknotRecognition/reports/` | Only the historical reference code needed by the retained tests |
| `patches/affine_families_and_inheritance.patch` | Integration patch: two modified files and fourteen new files |
| `baseline/` | Original versions of the two modified files at the pinned revision |
| `experiments/arithmetic/` | Standalone arithmetic stress tests and peripheral-reduction audit |
| `experiments/geometry/` | Independent rational/native geometry audit and inherited meridian fixture construction |
| `examples/cyclic_families/` | Five exact family inputs, certificates, and replay checks |
| `examples/normal_intervals/` | Sharp local fixture and 128-tetrahedron meridian, complete extractions and orbit-input files |
| `results/` | Recorded measurements and exact comparison counts |
| `validation/` | Baseline/final test logs, source and patch audit, and artifact validation |
| `CLAIM_LEDGER.md`, `CLAIM_LEDGER.json` | Proved, implemented, measured, and unresolved claims |
| `PROVENANCE.json`, `source_manifest.json`, `SHA256SUMS` | Source revision, attribution, runtime, and file integrity |

Unrelated historical benchmark result archives are omitted. The 362 retained source files include all code and fixtures needed for the complete integrated test suite.

## Reproduce

The core implementations and quick checks require only the Python standard library. Python 3.12.14 was used in the recorded run.

```sh
python scripts/check_hashes.py
python scripts/reproduce.py quick
```

The quick route runs the 65 methods in the new/restored modules, the rational geometry audit, stored family certificates, and the peripheral reduction check. It writes fresh logs under `reproduction/` and preserves the recorded evidence.

For the optional Regina audit and figure generation:

```sh
python -m pip install -r requirements-audit.txt
python scripts/reproduce.py full
```

To rerun the separate performance measurements:

```sh
python scripts/reproduce.py benchmarks
```

To regenerate the exact example artifacts, tables, and figures:

```sh
python scripts/check_family_examples.py --regenerate
python scripts/make_normal_examples.py
python scripts/make_tables.py
python scripts/make_geometry_figures.py
```

To rebuild the article, using a normal TeX Live installation with `latexmk`:

```sh
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error unknot_affine_families.tex
```

`make` in the article directory invokes the same compilation. The bibliography is embedded in `sections/bibliography.tex`; no BibTeX service or external bibliography database is required.

## Integrate into ProveIt

The immutable baseline is:

```text
ea9cf443c8ce33e09ed0c48b0ef7856ddf6326a3
```

In a clean checkout at that revision, review and apply:

```sh
git apply --check /path/to/affine_families_and_inheritance.patch
git apply /path/to/affine_families_and_inheritance.patch
```

The patch was independently applied in a fresh directory; all 16 affected outputs matched the distributed source byte for byte. All 346 unmodified distributed source files match pinned Git blobs, and all 14 additions are absent at that revision. The audit is in `validation/patch_validation.json`.

If integrating on a later revision, review overlaps with already merged incoming work. The polynomial-projector implementation, two-field fixtures, and their original tests are inherited unchanged; their hashes are recorded. The `normal_surface.py` communication correction is also an unchanged inherited fix. Ordinary commutant reuse defaults on only within the existing optional Fitting backend. Primary search, saturation-locality stopping, and one-generator inheritance remain separately opt-in.

Place the article and supporting research files in the repository's chosen report or incoming-document location. The patch does not allocate a report number. No remote branch or pull request was created by this work.

## Next research priorities

The article proposes eighteen research questions with explicit milestones. The most consequential are completing residual face/edge attachments and boundary-pattern transport; integrating general weighted interval-orbit reduction; certifying cyclic blocks with a coverage theorem; identifying tractable geometric peripheral constraints; measuring algebra activation on difficult residual knots; and proving bounds on the number and encoding size of all hierarchy states, including resets.

A conditional composition theorem explains exactly how these obligations would yield the targeted `exp(O(log² n))` running time. The present subroutines establish particular operation-cost claims under their contracts, without establishing those global hypotheses.

## Attribution and license

The new work follows ProveIt's MIT No Attribution license. Included pre-existing components retain their accompanying license notices. Prior code and fixtures are credited in the article, `PROVENANCE.json`, and `primary_research/INHERITANCE_PROVENANCE.json`.

The article contains conventional proofs supported by independent finite oracles and separate model-assisted review. It is not represented as proof-assistant-verified or externally peer-reviewed. External article PDFs and downloaded reference slide decks are not included.
