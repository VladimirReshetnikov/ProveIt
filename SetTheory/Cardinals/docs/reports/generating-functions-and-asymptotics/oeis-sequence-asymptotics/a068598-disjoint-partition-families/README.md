# Report163 Growth bounds for maximal families of disjoint partitions

Report163.pdf is the nine-page mathematical report; Report163.tex is its
complete editable LaTeX source. Report163_Source.zip packages the report,
source, bounded exact Python companion, frozen diagnostic data, tests,
source provenance, and deterministic local release tools.

## Mathematical result

For OEIS A068598, with inclusion-maximal unordered families of pairwise-
disjoint strict partitions and a(0)=1,

    1/5 <= liminf log(a(n))/(n log n)
        <= limsup log(a(n))/(n log n) <= 1/4.

The explicit elementary upper bound is

    a(n) <= 3^(n-1) n^floor((n-2)/4), n>=2.

The queens injection gives a(n)>=Q(floor((n-1)/5)) and uses Luria and
Simkin's proved all-integer lower bound on ordinary labeled queens
configurations. Its linear correction is only a one-sided lower estimate.
The separate elementary construction proves

    a(n) >= 2^k k!, k=floor((n-1)/7), n>=8.

Every fixed A exp(B n^c), A,B>0 and c>1, has a(n)/(A exp(B n^c))->0.
This rules out both posted c>1 fits as asymptotic equivalents, without
judging their finite-range numerical fit.

For N(y)=min{n>=0:a(n)>=y}, the leading-scale constants lie between 4 and
5. No monotonicity of a(n) is assumed. Finite elementary Lambert-W brackets
are also proved for every real y>1. The companion uses exact integer
powers/factorials instead of floating-point W to provide finite brackets.

The report does not establish existence of a limiting coefficient, its
value, a multiplicative equivalent, or a transseries. A clearly labeled
unproved quadruple-decomposition direction is not promoted to a theorem.

## Quick verification

Requirements: Python 3.10 or later, standard library only. Tested with
Python 3.12.14. From this trusted report directory:

    python -B companion/disjoint_partitions.py verify
    python -B companion/disjoint_partitions.py threshold --value 1000 --max-n 24
    python -B companion/disjoint_partitions.py bounds --value 100000000000000000000
    python -B -m unittest discover -s companion -p 'test_disjoint_partitions.py' -v
    python -B -O -m unittest discover -s companion -p 'test_disjoint_partitions.py' -v
    python -B -m unittest test_release -v
    python -B -O -m unittest test_release -v
    sha256sum -c SHA256SUMS

The production companion does not use network, input files, or file-write
APIs. -B suppresses interpreter bytecode caching. Full command semantics,
strict bounds, integer validation, JSON conventions, and diagnostic limits
are in companion/README.md. The tests and release utilities do read files
and make disposable or explicitly named output files.

All 14 companion tests and 11 release tests pass in normal and optimized
modes. Normal/-O production JSON outputs are byte-identical. Full default
verification checks all 179455 matchings without the forced singleton
through n=24, maximal-clique counts through n=18, queens extensions through
k=8 for all five rounding residues, 24 greedy examples, and rounding
identities through n=100000. Counts, source excerpts, and complete checks
are frozen in data/. Source terms beyond n=24 are attributed source data,
not independently enumerated counts. Finite computation is diagnostic;
the article's proof and its cited external theorem establish the limits.

A complete 14-test suite took about 19 seconds on the author's build
machine. This is an observation, not a runtime guarantee.

## PDF reproduction

The tested TeX engine is pdfTeX 1.40.26, TeX Live 2025/dev/Debian.
Required packages appear in Report163.tex: Latin Modern, AMS packages,
mathtools, geometry, booktabs, array, microtype, and hyperref. The local
TeX distribution and its font maps must be installed in the standard
locations used by build_pdf.py. No network or package installation occurs.
Linux/POSIX with /proc/self/fd and no-follow directory descriptors is
required for the release helpers.

Choose an already existing trusted parent directory. Both build output
paths must be new, even if a path contains an apparently harmless empty
directory or dangling symlink. For example:

    python -B build_pdf.py --output-dir /home/alice/results/report163-build-one
    python -B build_pdf.py --output-dir /home/alice/results/report163-build-two
    cmp /home/alice/results/report163-build-one/Report163.pdf /home/alice/results/report163-build-two/Report163.pdf
    cmp Report163.pdf /home/alice/results/report163-build-one/Report163.pdf

The builder copies the source into a new descriptor-pinned directory,
rebuilds the pdflatex format in isolated writable TeX directories, disables
shell escape, fixes SOURCE_DATE_EPOCH, suppresses changing PDF metadata,
and reruns until references stabilize. It rejects settled warnings,
overfull/underfull boxes, and missing characters. It does not overwrite
existing output. A different TeX installation may change PDF bytes while
preserving mathematical content; byte identity is toolchain-specific.

All nine pages of the final PDF were rendered and visually inspected.
Two final clean builds in the tested environment were byte-identical to
the released PDF and had settled warning-free logs.

## Reproducible archive and no-clobber output

SHA256SUMS records a sorted fixed allowlist of all 14 release payload
members; it is included as a fifteenth archive member. make_zip.py checks
all allowed payload hashes before producing a ZIP. It includes no other
files from the source directory. Local build logs, render images, earlier
archives, and author-only review records are intentionally excluded.

    python -B make_zip.py --output /home/alice/results/Report163-one.zip
    python -B make_zip.py --output /home/alice/results/Report163-two.zip
    cmp /home/alice/results/Report163-one.zip /home/alice/results/Report163-two.zip

ZIP members are stored uncompressed in sorted order with fixed
2026-10-03 timestamps and fixed permissions. Two archive constructions
were byte-identical. Repacking an independently extracted allowlisted
bundle preserves the bytes. The archive has no absolute or traversal
member names and requires no external mathematical files.

The output helpers reject parent traversal, symlink components, existing
outputs, nonregular source files, and missing parent directories. They
use exclusive creation and descriptor-pinned parent traversal; regression
tests include a replaced-parent scenario. Parent directories and the local
Python/TeX toolchain must be trusted. These tools do not claim isolation
from a hostile same-user process that can replace newly created directories
or executables. They do not install software or change permissions on
existing files. They must not be treated as a sandbox for hostile code.

Checksums detect accidental changes relative to the supplied manifest.
They are not authenticated signatures: someone replacing both source and
manifest can create a different package. Obtain a trusted archive digest
and review code if provenance matters. Do not silently regenerate the
manifest after a failed integrity check.

## Source boundaries

SOURCE_PROVENANCE.json gives URLs, versions, snapshot hashes where
available, precise inspected locations, and limits of the source check.
The upper proof credits Spencer's mass inequality via Nathanson p.108;
the stronger lower proof credits Luria and Simkin's Theorem 1.1.
Filaseta's 1996 chapter was identified from its publisher abstract and
metadata; its full text was not read. This is a bounded literature check,
not an exhaustive novelty or priority certificate. Full third-party
papers and full OEIS entry prose are not redistributed.
