# Source and build audit

## Computational provenance

The Report182 exact finite algorithms were written independently of the original
research scripts. They use an unbounded coin-change algorithm for ordinary
partitions, a descending 0/1 product algorithm for the weighted coefficients,
and separately derived divisor/logarithmic-derivative recurrences. Direct
partition enumeration and low-hole construction do not import a precomputed
q-bracket or decomposition implementation.

The source snapshot under `data/references/exact_checks_frozen.py`, reference
integer sequences, exact result object, and earlier hole-constant enclosure
record are frozen inputs. `data/PROVENANCE.json` records their origin and hashes.
The operational core is adapted only for a read-only verification interface;
all arithmetic and finite domains are preserved. `code/verify.py` contains
literal SHA-256 pins for the selected reference inputs. It recomputes results
before comparing them with the frozen certificate and integer sequences.

The earlier enclosure record is only a cross-check: the delivered tighter
hole intervals are computed from exact partition numbers with integer rounding
and independent rational tail formulas. The verifier checks that each new
interval lies strictly inside its earlier counterpart. It does not treat the
earlier decimal values as a substitute for deriving the new intervals.

## Second-correction supplement

The additional standard-library Fraction implementation in `code/second_order.py`
was independently reviewed against two earlier reconstructions. It uses exact
Gaussian elimination and sparse polynomials, with no SymPy dependency. Its
separate certificate, reference hashes, and corruption guards cover the three
weight-8/10/12 brackets, their nonzero determining determinants, every Laurent
coefficient, and A2/B2 algebra. The manuscript's homogeneous-span and analytic
transfer theorems remain explicit inputs. The frozen SymPy source is included
only for provenance and is never imported or executed by mandatory checks.

## Infrastructure provenance and audit

The builder, manifest checker, and build-guard tests were adapted from the
Report181 scaffold after reading their full source. The Report181 mathematical
core, coefficients, formulas, and claims were not carried into this package.
Its hard-coded report identity, source inventory, generated filenames, build
scope metadata, and report-specific guard expectations were replaced.

Retained mechanisms are explicit source inventories, nonsymlink regular-file
checks, strict JSON parsing, exclusive new-output creation, temporary build
workspaces, environment isolation, no-shell-escape compilation, stabilized
auxiliary files, TeX log rejection, sorted uncompressed ZIP entries, fixed
metadata, exact inventory hashes, and normal/optimized check equivalence.

The infrastructure guards exercise missing/extra files, malformed/duplicate
JSON, symlinks, FIFOs, path traversal, source/output overlap, cache entries,
unexpected empty directories, corrupted hashes, wrong PDF signatures, TeX log
defects, nonstabilizing TeX runs, subprocess failure, differing normal/optimized
results, and publication races. They use synthetic TeX outcomes. Actual TeX
compilation and extracted-release rebuild are checked separately.

## Scope separation

1. Exact integer/rational arithmetic establishes the stated finite identities
   and explicit constant enclosures within the documented finite ranges
2. Finite coefficient agreement does not prove any asymptotic theorem
3. Binary64 phase/carrier computations are optional diagnostics, not rigorous
   intervals and not part of the exact verifier
4. Analytic localization, remainder, and inversion claims must be read in the
   mathematical report; no software assertion upgrades them automatically
5. There is no effective onset bound, finite-n coefficient-accuracy theorem,
   or general all-orders symbolic engine in this package

The release is a local artifact. Building it performs no upload, publication,
repository mutation, or external service write.
