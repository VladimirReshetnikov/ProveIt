# Lossless DFS ledgers

The `*.ledger.gz` files retain every TSV event from the searches, in its original
order. The archive removes deterministic fields and run-length encodes the
remaining events before applying gzip. It does **not** replace the ledgers with
summary statistics. The adjacent JSON files record the original byte counts and
SHA-256 hashes, packed hashes, event counts, group metadata, and completed
verification results. `index.json` collects the six retained ledgers.

The compiler front end is `../ledger_codec.py`; its streaming implementation is
`../ledger_codec.cpp`. Requirements are Python 3.9 or newer, a C++17 compiler,
zlib development files, and OpenSSL development files. Set `CXX` if the compiler
is not named `c++`. The helper builds automatically in a temporary directory.
No Python packages are required.

From the directory containing `ledger_codec.py`:

```sh
python3 ledger_codec.py verify packed_ledgers/all_actions.ledger.gz
python3 ledger_codec.py unpack packed_ledgers/all_actions.ledger.gz all_actions.ledger.tsv
python3 ledger_codec.py pack all_actions.ledger.tsv repacked.ledger.gz --choices 1008
python3 test_ledger_codec.py
```

`verify` reconstructs and hashes the entire original TSV byte stream without
writing a large output file. `unpack` writes those same bytes, checks their
stored SHA-256, and then publishes the restored file. `pack` likewise verifies
the complete reconstruction, independently hashes the original with Python's
`hashlib`, and only then publishes the packed file. Existing output files are
preserved unless `--force` is supplied. To compare against a separately retained
raw ledger, use `verify PACKED --raw ORIGINAL.tsv`.

## Deterministic fields

The search starts each deletion group with all incoming-edge assignments equal
to `-1`. Its pending work is a stack. An event consumes the top assignment.
A `branch j` event creates children by replacing coordinate `j` with each action
in descending order, so that the next visited child has action zero. `prune`
and `survivor` create no children. Given the choice count, group degree, and
ordered branch events, induction on the event index reconstructs every
assignment exactly. A prune weight is `choices ** number_of_unknown_coordinates`;
branch and survivor weights are respectively zero and one, as in the original
writers. The event's case index or needed coordinate and its reason code remain
explicitly encoded.

This reconstruction supports groups whose DFS completed and a final group cut
off with pending work. It also supports changing degrees between groups. A
partial ledger remains partial after compression. The separate search summary
and frontier files retain the distinction between visited groups and groups
never entered before a time limit. Compression does not certify the truth of a
pruning reason; the search and independent replay artifacts address that issue.

## Binary format, version 1

The gzip stream contains the following uncompressed byte sequence. Unsigned
integers use canonical little-endian base-128 variable-length encoding: seven
data bits per byte, with bit 7 indicating a following byte. Signed event values
use zigzag encoding (`2*n` for nonnegative `n`, `-2*n-1` for negative `n`).

1. Eight magic bytes, `50 4c 45 44 47 31 0d 0a` (`PLEDG1` and CR/LF).
2. One format byte: `1` for the original two assignment columns, `2` for the
   generalized comma-separated assignment column.
3. Choice count, header length, and the exact original header bytes including LF.
4. Records, each beginning with a one-byte tag:

| Tag | Fields following the tag |
| --- | --- |
| `0` | Group index, deleted state, incoming degree; all unsigned varints. |
| `1` | Run length; one outcome byte (`0` branch, `1` prune, `2` survivor); signed event value; unsigned reason. |
| `2` | Original byte count, event row count, group count; then the original 32-byte SHA-256 digest. This is the final record. |

Event runs never cross a group boundary. All records omit the TSV fields
determined by the DFS. The two literal headers are preserved and checked by the
decoder. All emitted rows use canonical decimal integers, tabs, commas where
applicable, and LF. The codec currently accepts degrees 1 through 12 and checks
that weights fit unsigned 128-bit arithmetic; the retained experiments require
only degrees 1 through 9. It rejects an event after a group's work stack becomes
empty, a new group before the preceding one completes, a branch on an already
assigned coordinate, invalid event codes, truncated input, and mismatching
reconstructed byte counts or hashes.

## Verification scope

For each retained ledger, `pack` checked the reconstructed SHA-256 against both
the C++ streaming hash of the untouched original file and an independent Python
streaming hash of that file. The metadata's `verification.verified` field records
that result. The test script additionally writes and byte-compares small restored
fixtures covering both headers, changing degrees, repeated events, a survivor,
partial traversal, a 128-bit weight, and an empty ledger; it checks rejection of
malformed assignments, a wrong choice count, a changed checksum footer, a missing
terminal newline, and an unrequested overwrite.

The original raw files were preserved during packing. Gzip output bytes can
depend on the zlib implementation even when the raw ledger bytes are identical;
the raw digest is the reproducibility criterion for a repacked artifact.
