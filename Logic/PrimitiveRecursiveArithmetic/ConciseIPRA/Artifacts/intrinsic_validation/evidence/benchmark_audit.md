# Pinned complexity audit

Repository commit: `fc05b10f0e03f22edbfdde9298a29fb2fee5dc59`.
Runtime: CPython 3.12.14, matching the repository's metric convention.

The initial package table in README is stale as a complete frontier summary. Its later intake paragraphs update the integrated strict frontier, and its current Artifacts tree contains 21,514 entries and 3,200 Python files. The entire Artifacts tree was retrieved with `truncated=false`.

## Independent bounded census

All Python blobs under 1,800 original UTF-8 bytes were downloaded, Git blob hashes verified, and statically parsed/normalized without execution: 1,272 path occurrences, 681 distinct blobs, zero download failures. This is a bounded candidate census, not a complete census of every Python file; comments can make a small normalized program exceed the raw-byte threshold.

Artifacts minima confirmed among legitimate checker implementations:

| Coordinate holder | Tokens | AST nodes | Normalized bytes |
|---|---:|---:|---:|
| `fused_blocks_and_checkers/checkers/code/checker_tokens239.py` | 239 | 261 | 549 |
| `checked_reduction/compact/checker_ast255.py` | 245 | 255 | 580 |
| `prefix_conditional/code/checker_bytes461.py` | 267 | 298 | 461 |

Selected compact controls are in `reference/compact/`. `evidence/bounded_census_index.json` maps Git SHAs to repository paths, and `evidence/bounded_census_metrics.json` records normalized measurements and SHA-256 hashes.

The independent incoming ZIP audit establishes a later compact 460-byte program, then a general-context sequent 458-byte program. The 455-byte and 238-token seeded-context variants require an external context convention and should be shown separately. The strict sorted-JSON envelope is 302/340/584; restricted-expression input is 299/338/575. The exact actual-binding grammar family is 321/361/627. Each triple is a coordinatewise envelope attained by different programs.

## Mathematical and contract qualifications

- These are observed upper bounds on the unknown minimum description size. They are not proved lower bounds on all equivalent axiomatizations.
- The compact checkers assume canonical guarded Eq/D public goals and an integer/list certificate alphabet. They do not validate those promises themselves.
- The sorted checkers validate a broader sorted grammar that includes noncanonical administrative aliases. Their full completeness claim is specifically for canonical public encodings.
- The exact actual-binding checkers validate precisely the intended canonical Eq/D grammar.
- Arbitrary sequent inputs certify `Gamma |- A`; accepting an input with a false assumption does not certify `A` as a theorem.
- A generic proof-verification VM with its entire theory axiom/compiler table external to the measured source is not a fair smaller complete presentation.
- None of the ten inspected incoming reports claims the requested below-all-frontier mathematical construction. Several explicitly state that it was not achieved.

No new valid checker below the combined compact frontier has been found in this audit. No arithmetic axiom deletion follows from source metrics alone.
