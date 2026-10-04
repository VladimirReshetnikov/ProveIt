# Model-performed independent review of Report65 release tools

Date: 2026-10-04. This review concerns the initial frozen tool versions. A later
delta review, if present, determines acceptance of patched versions. This is a
model-performed source review and executable test exercise, not human inspection
or formal verification.

## Result

The baseline candidate rebuilds exactly, including from an extracted ZIP and under
hostile inherited TeX configuration. Repeat archives are byte-identical. The
adversarial suite obtained all 82 expected outcomes; four of those outcomes
deliberately demonstrate missing checks rather than successful rejection.

Three fixes are required before describing the tool as a sealed artifact
consistency checker: compare the derived flattened source and rebuilt PDF with
their sealed hashes; compare the exact sealed directory set; enforce the canonical
manifest permission bits. The manifest-mode issue applies to both ZIP checking and
filesystem verification.

## Reviewed pins and scope

- Builder: `6621846e17f583ad555465b9ad03aececaed40c3573073c1c51c062495958cc1`
- Release tool: `b87f8681a8977f99085f4d296d7436fa06d28e244e7f59d481463ae758c9fef8`
- Dependency lock: `655822c2dee2f0f4d1a0a8d00208579e4a53d558ce8ca385557e1d88c5e614e2`
- PDF: `2c1fe34d39e6635a98332e9a2c3e123c902f980861141234012716ab20b6069f`
- Flattened TeX: `bd2d25b0dc791ceb05a06e4fa414319568fdbe36226891dec3ab0ee733a39dd9`

The README and both complete release scripts were inspected before execution.
The candidate was copied into a newly owned review tree. Seal, mutations, output
directories, and archives were confined to fresh review-owned paths. No inherited
research or audit mathematical code, physical simulator, saved-schedule execution,
native interpreter, or Lean was imported or executed. The only report code run was
the inspected fresh release tooling and newly inspected independent review drivers.
System TeX/PDF tools and unzip performed the ordinary document/archive operations.

## Positive findings

1. Both tool pins, the lock pin, and the initial deliverable pins matched exactly.
2. The owned copy sealed, passed complete verification with `--metadata --origins`,
   and refused resealing. All 49 original input files remained unchanged.
3. A locked build, a build with hostile inherited TeX/path/home/locale/date settings,
   and a locked rebuild of the ZIP-extracted tree produced precisely the expected
   PDF, flattened source, and 266-system-input dependency lock. All successful
   receipts contain no selected layout warnings. The PDF is 20 pages.
4. Two source ZIPs were byte-identical:
   `fc101867b68f76b0fea90a0b7a5c891b2fe0e3aff0376e7f6cea12e815f79e95`.
   Their owned-copy manifest pin was
   `131ae03a5ec71de9c28ee881fd373f29a67e5b524ea0f6018f6529dddf425784`.
   This is a review-copy pin, not a final release trust anchor.
5. Ordinary Info-ZIP extraction passed default release verification. As documented,
   `--metadata` rejected canonical archive timestamps in place of original
   nanosecond file modification times.
6. Bad manifest/lock digests, altered executable/input lock entries, invalid locked
   paths, missing lock, existing/overlapping output, symlinked output parent, sealed
   draft mode, and the exercised invalid source trees failed before creating their
   proposed fresh output. Existing output sentinels were preserved.
7. The checker rejected changed/missing/extra files, changed ordinary file modes,
   source symlinks, directory symlinks, FIFOs, changed manifest bytes, invalid or
   duplicate input pins, bad input hashes, and empty directories at seal time.
8. ZIP checking rejected duplicate/extra/missing members; absolute, parent, dot,
   empty-component and backslash paths; explicit directory members; nonregular
   attributes; changed bytes, ordinary file modes, timestamps and manifest bytes;
   and encrypted member flags. It neither extracted nor executed archive members.

## Reproduced gaps and narrow remedies

### G1: sealed rebuild success did not establish artifact equality

The builder verified input hashes but only recorded its output hashes. In an owned
copy, appending harmless comments to the delivered flat TeX and PDF, then sealing
that distinct copy, yielded a successful build even though both rebuilt output
hashes differed from the sealed deliverables. The baseline itself is consistent;
this is a missing enforcement check, not evidence that its article was wrong.

Remedy: compare the derived flat TeX hash against the manifest before creating the
output; compare the rebuilt PDF against its manifest hash before promoting final
deliverables or writing a success receipt. A late PDF mismatch necessarily leaves
diagnostic build files; do not promise all build failures occur before any output.

### G2: sealed builder ignored extra empty directories

Adding an empty directory to a sealed owned copy made release verification and
archive creation fail, but the builder succeeded. It compared file sets only.

Remedy: compare the canonical sorted directory set too. Snapshot directory metadata
before and after if the documentation promises metadata preservation for them.

### G3: manifest's own mode was unchecked

Changing the archive manifest mode from 0644 to 0777 passed archive checking because
the manifest branch skipped the mode comparison. A filesystem copy whose manifest
was chmod 0777 also passed `verify --metadata`; the manifest is outside its own file
ledger.

Remedy: specify and enforce canonical mode 0644 for the manifest in filesystem and
ZIP checks and sealed-build preflight. Ensure seal explicitly creates that mode
even with a restrictive caller umask.

## Supplemental boundaries

- A ZIP entry with a changed creator-host field was accepted and extracted to the
  expected 0644 file here. No permission failure was demonstrated from that case.
- Central Unicode path extra fields were rejected in both the main Python 3.12.14
  runtime and the separately tested system Python 3.13.5 runtime. A local-only
  Unicode extra field was accepted by archive-check but generated an unzip warning;
  unzip retained the intended central path. This is a canonical-format hardening
  opportunity, not a demonstrated unsafe-path bypass in this environment.
- The interpreter, its standard library, the OS, shared libraries and system TeX
  configuration resolution are not comprehensively locked. The executable/input
  lock and recorder checks should not be described as a general hostile-code
  sandbox or proof of reproducibility on every Python/OS/TeX installation.
- The sparse TeX primitive filter is not a complete TeX security parser. The
  independently supplied trusted manifest authenticates the approved article.
- Reads can affect access times. Preservation evidence covers bytes, byte size,
  modes, modification times and change times, as used in source pins; it does not
  claim preservation of access times.

## Evidence map

- `RESULTS.json`: 82 expected outcomes, argv, exit codes, absence-of-output checks
- `review_tools.py`: independently authored, inspected test driver
- `review.stdout`, `logs/`: complete subprocess transcripts
- `outputs/`: independent normal, hostile and extracted locked builds
- `candidate-before.json`, `candidate-after.json`: original candidate inventories
- `origins-before.json`, `origins-after.json`: all 49 original-input inventories
- `ZIP_METADATA_RESULTS.json`, `FINAL_EDGE_RESULTS.json`: supplemental observations
- `owned-release/`, `cases/`, `mutant-archives/`: owned reproduction fixtures

Initial result ledger SHA-256:
`2447120871f22d87a63fb86429eb53619f58bac3faece4449a9a7b0df885afcb`.

The original candidate and pinned origins were not mutated by this review. The
owned sealed base also retained its complete inventory after all tests. Any later
author changes require a separately pinned fresh-copy delta review.
