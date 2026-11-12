INDEPENDENT STATIC BASELINE CENSUS
==================================

Pinned repository: VladimirReshetnikov/ProveIt
Commit: 42fba2a76aea6eb41a8c4acfe7761620f58956ee
Normalization runtime: CPython 3.12.14

Result
------
The surveyed sources confirm the combined observed coordinate envelope
249 significant tokens / 271 AST nodes / 495 normalized UTF-8 bytes.
Three DIFFERENT programs in the incoming three-field archive attain those
coordinates. No surveyed candidate improves on that envelope.

Research-only observed minima are 251 tokens / 275 AST nodes / 502 bytes,
again attained by three different programs. Incoming archives therefore
matter to the comparison.

Scope and method
----------------
The pinned Research tree contains 5,935 Python paths and 1,446 unique Git
blobs. EVERY Python file was selected, with no raw-source size cutoff.
References, controls, and frozen source-corpus copies were included, rather
than excluded by filename. Every blob was downloaded at the pinned commit and
verified with the Git blob hash SHA1("blob " + byte_length + NUL + data).
All 1,446 blobs were verified; 1,445 produced canonical measurements.
The remaining blob is a valid readable reference checker with a class
containing only a docstring. The exact shared docstring-removal normalizer
leaves that class empty, producing an unparsable class suite. Its unparse
already has 1,844 bytes and 367 tokens; inserting one diagnostic pass yields
1,853 bytes / 368 tokens / 414 AST nodes. It is therefore far above every
coordinate of the envelope. This exception is recorded in exclusions.json;
the diagnostic repair is not silently substituted into the canonical metric.

In addition, every Python member of every ZIP archive in the pinned docs
tree was inspected, with no size cutoff. This covers all three incoming
archives, 36 Python member paths, and 33 unique sources. The three ZIP
bytes were verified against their pinned Git blob hashes. No parse or
measurement errors occurred.

The analysis removes leading docstrings in modules, classes, ordinary
functions and asynchronous functions, runs ast.unparse, and appends one LF.
It counts significant tokenize tokens, ast.walk nodes after reparsing the
normalized text, and the UTF-8 byte length. No downloaded Python code was
imported or executed.

Candidate triage identifies a JSON import, a print call, and the literal
ACCEPT marker. It yielded 792 measurable Research candidates and 21 incoming
candidates. The three Research coordinate minimizers were inspected
directly: each has its checking recursion, scope-opening implementation,
JSON input and ACCEPT output, and imports json only. The four surveyed
Research sources with a JSON import and fewer than 495 normalized bytes
are manifest verifiers, not proof checkers.

All 112 other measurable files with at least one coordinate below the
incoming envelope were screened separately. None has a direct standard-input
operation (open(0), input(), or a stdin attribute) or the literal ACCEPT
marker. They are report/code builders, source-metric utilities, manifest
checkers, certificate/test utilities, or harnesses delegating to separately
charged programs. Their paths, metrics, imports, functions, calls, and module
docstrings are retained in exclusions.json for inspection.

Limitations
-----------
There is no raw-source size cutoff. The static candidate heuristic can miss
a different acceptance convention; the sub-envelope exclusions were therefore
screened separately as described above. This is not a correctness proof
for every candidate, and no absolute lower-bound theorem is asserted.
The compact guarded-public-language contract must remain distinguished from
a complete public-goal grammar validator. The measured coordinates of
different programs must not be combined into the size of one program.

Files
-----
summary.json: concise result, coordinate-minimizing source identities,
              archive hashes, manually inspected exclusions, and limits.
census.json: full Research-source measurements and all path aliases.
incoming_census.json: full incoming-archive member measurements.
exclusions.json: every sub-envelope noncandidate and the accounted-for
                 normalization exception.
census.py: reproducible pinned download, Git verification and static audit.
audit_incoming.py: reproducible ZIP verification and static member audit.
inspect_exclusions.py: reproducible exception and low-metric screening.
summarize.py: concise receipt construction from the complete audit outputs.
research_metadata.json and incoming_metadata.json: pinned source-entry
                 manifests, allowing the audit directory to stand alone.
blobs/: exact downloaded Research sources, named by Git blob SHA.
normalized/: measured normalized Research sources, also named by Git SHA.

The scripts are audit utilities. They are not trusted dependencies of any
proof checker and must not be counted as if they were an arithmetic result.
