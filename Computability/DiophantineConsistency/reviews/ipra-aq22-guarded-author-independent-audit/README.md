# Independent audit of the AQ22 guarded author run

This artifact audit checks the historical author-only run preserved in
[`ipra-aq22-guarded-author`](../ipra-aq22-guarded-author/). It is not a
second Lean compilation. `audit.py` independently reads the pinned manifest,
Git source blobs, copied sources, logs, object files, recorded direct imports,
the earlier independent parent audit, parent outputs, provider artifacts and
overlay guards. It compares all 94 diagnostic occurrences in order, including
repeated declaration names, and checks the native and standard endpoint
statements explicitly. It checks the recorded terminal wrapper return code;
the audit's own terminal result is recorded separately.

The standard endpoint relates the AQ22 literal's positive-shift no-zero
sentence to the Gödel–Gentzen translation of the embedded Foundation ZFC
consistency sentence. The selected consistency translation is also linked to
negated mapped native refutation. These statements should be read with the
specified embeddings and translation in place.

The script requires the original temporary directories and Git objects to
remain available. It refuses optimized Python because its assertions are
part of the audit. It runs at idle CPU and I/O priority and limits aggregate
hash reads to 8 MiB/s. `receipt.json` records the exact checked state, files,
diagnostic names and scope; `terminal-observation.json` records the actual
audit process result.

The audit is a point-in-time check of recorded artifacts, not a matched peer
run, current-source replay, or claim about a PDF or degree. It does not prove
continuous absence of transient mutations, dynamically loaded dependencies,
or package-transitive source-to-object provenance. The Foundation provider's
build wrapper outer exit remains unobserved.
