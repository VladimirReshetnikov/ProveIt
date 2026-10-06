# Report 139: polynomial order for exactly one 1432

This self-contained offline companion contains the editable LaTeX article,
its PDF, two independent exact integer implementations, a complete finite
obstruction certificate, a strict read-only verifier, and source provenance.
It proves the order b_n = Theta(9^n/n^3) for OEIS A224182, equivalent by
reversal to permutations with exactly one classical 1432. The main order
proof is computer-free. It does not prove a leading equivalent, convergence
of b_n/(n A_n), the candidate amplitude ratio 3/80, or D-finiteness.

The general fixed-k lower corollary concerns 1 direct-sum decreasing(k),
with liminf b_n/(n A_n) >= k^(-2k-1). No general upper result is asserted.

## Requirements and quick start

Python 3.10+ with its standard library is enough for integrity, replay,
self-tests, and ZIP packing. PDF builds additionally require pdfTeX/pdfLaTeX
and the packages listed in Report139.tex. There are no network requests,
third-party Python dependencies, inherited report bundles, or research notes.

Isolated Python (-I) is mandatory. All executable modules first import only
built-in sys and reject nonisolated launches before any further imports.
Every check uses explicit exceptions, so optimization (-O) cannot remove it.

Let BUNDLE be the extracted Report139 directory and OUT an existing real
directory outside it. Every output target must be absent, and its parent
must already exist. No command overwrites an existing path or writes into
the bundle.

    python -I -B BUNDLE/verify.py check
    python -I -B BUNDLE/verify.py replay --output OUT/normal
    python -I -B -O BUNDLE/verify.py replay --output OUT/optimized
    python -I -B BUNDLE/verify.py selftest --output OUT/selftest
    python -I -B BUNDLE/verify.py build --output OUT/build
    python -I -B BUNDLE/verify.py pack --output OUT/Report139_reproducible.zip
    python -I -B BUNDLE/verify.py reproduce --output OUT/full-reproduction

The final command runs the adversarial tests, normal and optimized replay,
two fresh PDF builds, frozen-PDF comparison, deterministic packing, and a
fresh-extraction repack. It reports PASS only when both builds are byte
identical to each other and to the frozen PDF. Different TeX distributions
may give different PDF bytes; build reports the comparison, whereas reproduce
requires agreement and preserves its diagnostic outputs on failure.

The normal and optimized replay-result.json files must be byte-identical.
check validates hashes, complete inventory, and strict data schemas; replay
also independently recomputes every mathematical fixture field. The verifier
executes code only from bytes that have already passed manifest verification.

## Exact mathematics replay

code/primary.py implements the split as an exact word substitution, using
old values 3v and new values 3c-1, 3c+1. It recovers the source with the
marked inverse, checks uniqueness of marked images, and verifies inflation.
Its pattern counter is independently cross-checked against standardized
quadruples for every permutation of sizes four through six (864 cases).

code/coordinate.py does not import primary.py. It independently represents
the split by integer-coordinate points, tracks ancestors, counts patterns
by direct four-index inequalities, and implements the inverse independently.
Both implementations enumerate all 46,224 permutations of sizes four through
eight, checking all 5,102 single-occurrence sources and the complete minima
position-and-value skeleton refinement. Their exact minima distributions,
counts, and canonical skeleton-count digests agree. The digests summarize
large tables; equality of the full two pattern-skeleton dictionaries is
also tested inside each implementation.

The coordinate implementation checks all 75,419 restrictions retaining the
source core. It also examines every possible interior center of every
avoider of sizes six through eight. Local adjacency plus the four singleton
rectangles must produce precisely the split images of all unique sources
of sizes four through six; every candidate inverse and forward roundtrip
is checked.

The primary implementation checks all 314 marked-minimum inflations of
avoiders of sizes one through five, including injectivity. It verifies the
explicit unmarked collision, the Ferrers-board obstruction 106 versus 107,
and the sole-support counterexample with four source occurrences.

### Complete exact-image obstruction certificate

The article proves that any false positive in the eligible-center
characterization reduces to at most eight source points. For every source
of sizes four through eight with multiple occurrences, and every designated
core passing the four singleton-region tests, both implementations verify
that the split still contains a forbidden occurrence. The case counts are
0, 0, 6, 130, 1938, totaling 2,074.

checks/fixtures.json contains every one of these 2,074 designated cores,
its source permutation, exact split, and an explicit forbidden quadruple
in that split. All array indices in the certificate are zero-based. The
two implementations independently enumerate and reconstruct the entire
ordered list, including each lexicographically first witness. Thus the
certificate includes actual witnesses, not only claimed aggregate counts.
The verifier enforces its complete typed structure. Replay checks both
completeness and mathematical content by exhaustive reconstruction.

This certificate is used only for the additional exact-image theorem.
The main order theorem instead has the article's computer-free eight-case
split proof, interval inflation argument, entropy concentration, and the
cited growth-diagram and strip-asymptotic inputs. No machine-checked proof
of these analytical or combinatorial arguments is claimed.

## Integrity and output discipline

The manifest covers every payload byte except itself. The allowed files
and directories are hard-coded. Unknown and missing entries, symlinks,
nonregular files, duplicate JSON keys, nonfinite JSON constants, wrong
field types, boolean or floating-point integers, noncanonical rational
strings, unknown nested fields, malformed permutations, repeated certificate
records, and incomplete certificate inventories are rejected. A correctly
typed but false fixture is rejected by replay after its hashes are updated.

Self-tests mutate disposable external copies. They check changed code,
closed inventories, schema errors, hash records, false mathematical data,
nonisolated import shadowing, output containment, path traversal, symlink
ancestors, existing files, normal/-O agreement, and byte-identical repacking.
An unsealed argparse.py shadow is rejected before it can execute, including
under -O. File bytes are read with regular-file checks and no-follow flags
where supported. All output creation is exclusive.

This is an integrity and reproducibility seal, not an authenticated digital
signature or a security sandbox for hostile code. Someone who deliberately
changes the verifier and all matching hashes can create a different bundle.
Users should review source and obtain a trusted archive hash separately.

For maintainers only, seal validates the complete payload and schemas and
writes a proposed manifest to an absent external file. It never installs
that manifest or changes the bundle. After authorized source edits, review
and install it manually, then rerun replay, selftest, and reproduce:

    python -I -B BUNDLE/verify.py seal --output OUT/new-manifest.json

## Scope of conclusions

The inverse bound is an asymptotic inside-ceiling bracket. Its real,
unrounded width tends to 11/2. The two endpoint o(1) errors remain inside
the ceilings, so this is not an exact finite threshold rule or an effective
numerical certificate. The constants are C_-=C0/2187 and C_+=81 C0, with
C0=81 sqrt(3)/(16 pi). The proposed 3/80 is C1/C0, not C1 itself.

The published MRR proof displays a stronger one-step upper inequality.
This report does not rely on it and makes no upper-order or worldwide
priority claim. The split bound is proved independently. See SOURCES.md
and the article for precise source attribution and retrieval caveats.
