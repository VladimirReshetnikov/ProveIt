# Reproducibility: exact degree of the native history family

Python 3.10 or later, standard library only. No network access, package install,
or earlier report is needed for the default checks. Run these commands from this
directory (or replace the script names with their paths):

    python -B verify.py
    python -B -O verify.py
    python -B verify.py --integrity-only
    python -B test_integrity.py
    python -B -O test_integrity.py

The default verification writes its receipt to standard output. An optional
`--output receipt.json` destination must be outside this reproducibility directory.
The checkers use temporary output files and prevent bytecode writes; verification
compares the complete package inventory before and after execution.

## What the self-contained core checks

1. Exact file and directory inventory, no symlinks, every content hash, complete
   provenance, all 14 mandatory input pins, and the frozen research-manifest pin.
   The native proof is a mandatory pinned input, even though it is not executed.
2. All raw gates of the four small DAGs, for programs `[0]`, `[1]`, `[0,1,1]`,
   and `[2,0,1]`; exact degrees are respectively 712, 712, 1147, and 1234.
   A separately implemented formula and a pinned source receipt agree with the
   raw-DAG degree and leading-coefficient certificates. The 67-row native kernel
   and the complete one-plus-squares finalizer are structurally matched.
3. The cancellation identity is verified in a four-variable sparse integer ring.
   Leading-coefficient checks use both 17 and 1000000007; a zero coefficient is
   never treated as a total-degree lower bound.
4. Full univariate polynomial expansion modulo 17, without the cancellation
   rewrite, for all four raw fixtures and the quadratic substitution in `[0]`.
   Every coefficient agrees with an independent expansion of the pinned receipt.
   Additional direct-formula expansions cover repeated-zero and maximum-uint32
   edge cases. These are finite regressions; the general theorem has a proof.
5. Formula-level degree checks cover single-phase, repeated-exponent, all-zero,
   mixed, and maximum-uint32 tables, including an all-zero 17-phase case whose
   leading coefficient vanishes modulo 17 but not the second modulus.
6. Fresh-input tests cover `X=y^2`, `X=y^3+y*z+7`, and `X=y^2-z^2`.
   Weighted degree bounds and full ray expansions certify the predicted degree.
   The last example checks a nonuniform ray as well as the degree-dropping
   all-ones ray; it does not mistake the latter for the true total degree.
7. All 127 unchanged rows of the generic recoder are analyzed with symbolic
   degree pairs `a*k+b`, valid for every integer `k>=4`, in both free-port and
   constant-one-port modes. Structural witnesses attain `max(k+1,20)`.
   Twelve representative widths check the loader maximum `max(34,k+1)`.
   The seven outer-loader formulas are source-pinned transcriptions proved in
   `research/GENERAL_DEGREE_THEOREM.md`; the checker does not interpret or run
   their original Python implementation.

Each fresh scientific certificate must equal its frozen reference after removing
only elapsed-time fields. The normal and optimized frozen references are also
compared. Source paths in the native reference certificates have been reduced to
filenames; every scientific field is unchanged.

## Optional large universal regression

The large historical DAG is deliberately not bundled. Extract Report23 v1, then
supply its exact `reproducibility/frozen/arithmetic` directory:

    python -B verify.py --universal --source-dir <Report23-v1>/reproducibility/frozen/arithmetic
    python -B -O verify.py --universal --source-dir <Report23-v1>/reproducibility/frozen/arithmetic

`--universal` and `--source-dir` are required together. No directory is searched,
no earlier workspace is assumed, and no alternate filename is tried. Eight
mandatory historical inputs are authenticated against the original source hashes
listed in `PROVENANCE.json`. Historical Python files must use the archive's
inert `.py.txt` names. Missing or changed inputs cause a failure.

This pass reads all 3,600,546 gates of the frozen 397,488-phase program, with
`g=2030`, `N=797011`, and exact degree 69,339,973. It is a regression against an
already established universal specialization. It does not establish new
universality or degree minimality. The supplied historical files are checked
again after replay. The self-contained core always runs before this optional pass.

## Provenance and integrity

- `data/`: 14 byte-identical pinned source/data files; original Python is renamed
  to `.py.txt` and is never imported, compiled, or executed
- `research/`: the frozen manifest with a neutral publication-status field, the
  byte-identical supplementary proof, and inert original copies of the four
  newly written research checkers
- `checks/`: portable adaptations of those four new checkers only
- `certificates/`: frozen normal/optimized scientific reference certificates
- `PROVENANCE.json`: explicit original and portable byte counts and SHA-256
  hashes for every copied or adapted artifact, with transformations described
- `INPUT_PINS.json`: all mandatory bundled input hashes
- `INVENTORY.json` and `INVENTORY.sha256`: exact payload inventory and its digest
- `QA_RECEIPT.json`: release-preparation normal/optimized replay and mutation results

Portable checker changes are limited to inert-source filename resolution,
bytecode suppression, mandatory explicit certificate destinations, and filename-only
source/output reporting. Mathematical operations, conditions, moduli, fixtures,
and expected values are unchanged. Only newly written local checkers are executed;
original source Python is inert evidence.

The two native reference certificates replace only the five `files[].source`
directory prefixes with filenames. All other certificates are byte-identical.
Their original and portable hashes are recorded separately. The research manifest
changes only `publication_status` to `frozen research reference`. Its original
and portable hashes are explicit in provenance. A separate canonical-content
digest authenticates every other manifest field, including all entries and pins.
Original research
manifest hashes continue to describe original bytes, not renamed or sanitized
portable artifacts. Both identities are checked through provenance.

The inventory excludes its own two files to avoid a circular digest. The release's
outer inventory seals both of them. Local mutation tests reject changed DAG data,
source text, proofs, checker code, certificates, missing pins, extra files or empty
directories, symlinks, and missing optional source data. Exact integrity is an
accidental-change check; the outer release hash supplies the trusted archive anchor.
