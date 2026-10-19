FOUR COMPLETED AUDIT SEARCH FAMILIES

All four searches returned zero candidates within their stated scope. See
audit_search_receipt.json for the exact input hashes, compile and execution
argument arrays, logs, completed counters, and scope of each family. Paths in
that receipt are relative to this directory. The stdout candidate files are
empty by design. Elapsed times are operational metadata.

Requirements: a GCC-compatible C++17 compiler. No network or theorem prover.

The focused source-constrained follow-up can be reproduced with:

  g++ -O3 -std=c++17 tag_helper_restricted_domains.cpp -o tag_helper_restricted_domains
  ./tag_helper_restricted_domains input237.tm 5 5 65 65 source_neutral237.txt source_profile237.txt > tag_source_restricted237.txt 2> tag_source_restricted237.log

For other families, compile the named source and run the exact argv array in
audit_search_receipt.json. Keep a copy of the retained logs if rerunning in
place. The full tag/helper search took approximately 527 seconds in the
original environment; the focused follow-up took approximately 9 seconds.

The tag representation maps an old configuration in the deleted state q to
state p at the same head position, with the tape cell opposite q's common
external incoming direction toggled. Corresponding incoming transitions flip
their written bit and target p. The search synthesizes both rows of p, with an
optional helper chosen from 601 individually neutral substitutions. The
focused follow-up restricts p/q pairs to those involving labels 113, 172, or
204 because their observed contexts changed under source-invariant filtering.

The basic shifted-head family instead uses an inductively closed all-tape
window abstraction. It permits offsets +2 or -2 and leaves other retained rows
unchanged. The other three families use finite empirical profiles. None of
their negative outputs proves a state lower bound. Any discovered candidate
would require an independent all-tape or source-invariant unbounded simulation
certificate and an exact blank initializer proof.

These four searches are separate from the seven-family replay documented in
README-searches.txt and search_summary.json.

Attribution: these audit scripts were created for the 2026-10-19 research
package. tag_toggle_domains.cpp adapts the offset search implementation, and
tag_helper_domains.cpp and tag_helper_restricted_domains.cpp adapt the helper
search implementation from the parallel binary-search work in this package.
