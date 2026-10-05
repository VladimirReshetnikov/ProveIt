# Report182: phase-sensitive weighted strict partitions

This package accompanies Report182 on

    A(q) = product_{k>=1} (1 + p(k) q^k),

where p(k) is the ordinary partition number (OEIS A000041). The weighted
coefficient sequence a(n) = [q^n] A(q) is OEIS A271619.

## Contents

- `Report182.pdf` and `Report182.tex`: the mathematical report and its source
- `code/`: independently derived, standard-library exact finite checks
- `data/`: frozen certificates, exact integer sequences, and provenance
- `optional/`: separate, uncertified binary64 numerical diagnostics
- `build.py`, `verify_manifest.py`, and guard suites: offline reproducible build
- `SHA256SUMS.json`: exact inventory of every release file except itself

The source-only tree does not contain the PDF, generated results, or manifest;
the builder creates these in a new output directory.

## Verify

Python 3.10 or newer is required. The exact verification uses only its standard
library, integers, and exact rational arithmetic; no package installation or
network access is needed.

```
python -I -S -B verify_manifest.py        # extracted release only
python -I -S -B code/verify.py
python -I -S -B -O code/verify.py
python -I -S -B code/verify_second_order.py
python -I -S -B second_order_guard_tests.py
python -I -S -B guard_tests.py
python -I -S -B test_build.py
```

The finite checker may take a few minutes. It computes p(0),...,p(10000),
a(0),...,a(5000), independent recurrences through 600, q-brackets and conjugation
identities on 81,156 diagrams through size 35, and 174 low-hole cases containing
8,898 triples. A separately certified supplement reconstructs the three
weight-8/10/12 q-brackets from 2,714 partitions through size 20, verifies
nonzero determining determinants, and checks the exact A2/B2 correction algebra. The hole constants use outward-rounded pure-integer fixed-point
arithmetic with explicit rational tails. `README_CODE.md` explains the checks
and their limits.

## Rebuild

With a working installed pdfLaTeX distribution and its ordinary AMS/hyperref
packages, choose a new directory whose parent already exists:

```
python -I -S -B build.py --output /tmp/report182-build
```

The builder never overwrites an existing output directory. It runs all exact
checks and guards normally and under `python -O`, compiles with shell escape
disabled, rejects unresolved references and overfull boxes, verifies the full
manifest, and creates a sorted ZIP with fixed metadata. It publishes the PDF,
TeX, ZIP, and an external `ARTIFACTS.json` receipt. No network access occurs.

An intact extracted release is also valid input. Rebuild it to another new
directory, then compare the PDF, TeX, and ZIP bytes. Byte identity is scoped to
the same source and installed Python/TeX stack, not arbitrary software versions.
Do not add caches, notes, virtual environments, or diagnostic outputs inside the
source or extracted release: its inventory is intentionally exact.

## Important limitations

Finite exact checks are not proofs of asymptotic remainders or of their onset.
The manuscript contains the analytic arguments; the code does not certify an
effective asymptotic onset or finite-n accuracy theorem. In particular, the
leading eventual two-charge carrier is a poor approximation at the checked
moderate indices, including n=5000. Optional diagnostics display that failure.
No convergent full asymptotic series, general all-orders symbolic engine, or
interval-certified coefficient approximation is implemented or claimed.

The manifest detects accidental changes. It is not an authentication signature
and cannot detect coordinated replacement of both content and manifest. The
builder trusts the supplied source, Python/TeX installations, and PATH; disabling
TeX shell escape does not make this a sandbox for arbitrary hostile sources.
