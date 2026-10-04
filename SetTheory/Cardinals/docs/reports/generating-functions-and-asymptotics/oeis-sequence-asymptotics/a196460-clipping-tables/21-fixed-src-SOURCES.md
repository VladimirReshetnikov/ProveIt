# Source and execution boundary

All retrieval and work recorded here took place on 4 October 2026, UTC.
The packet is separate from Reports 69 and 70. No original was used as an
output destination, imported as code, chmodded, or retimestamped.

## Pinned local mathematical inputs

* `/workspace/shared/two-witness-tensor-compiler-20261004/ONE_WITNESS.md`,
  Section 6: SHA-256
  `9135dd0e829adb3190e99ed1b62f8d419f9f7540cfd92a1acd1635726fa7172c`
* `/workspace/shared/independent-low-arity-audit-20261004/AUDIT.md`,
  especially Sections 1, 8, 11--13: SHA-256
  `6bf14006170df1e126fb98d8e06ee97cfb51786f9ce11bcc0a37370a896d5afe`
* Source packet manifest: SHA-256
  `b243e39e0fd9698f9d610f0f6d2b17485a98df8e20a9412c1c38c65877a42c82`
* Accepted audit packet manifest: SHA-256
  `6852625bc450563eeda5ad96956e3ac18da64b95ca446c654da14f3b978594b3`

These files were read as inert text. The accepted classification is stated
and proved again in compact form in the new proof. This packet relies on no
POWER/Pell theorem, scientific simulation result, interpreter execution,
formal proof rebuild, or statement of physical dynamics.

## Primary public sources

### OEIS A196460

URL: https://oeis.org/A196460

The retrieved entry identifies the single sum in PROOF.md (1), attributes
the entry to Paul D. Hanna (2 October 2011), and credits the leading
equivalence a(n)~2^(n^2) to Vaclav Kotesovec (25 June 2013). Its displayed
links provide a term table, not a cited proof of the leading equivalence.
The internal-format and term-table retrieval attempts failed; the standard
entry and its first 13 displayed values were available. Our arithmetic
does not run the entry's Mathematica or PARI programs.

### Existing model-counting interpretation

Martin Svatoš, Peter Jung, Jan Tóth, Yuyi Wang, Ondřej Kuželka,
*On Discovering Interesting Combinatorial Integer Sequences*, 2023.

* Versioned record: https://arxiv.org/abs/2302.04606v1
* PDF: https://arxiv.org/pdf/2302.04606
* DOI: https://doi.org/10.48550/arXiv.2302.04606
* Location: Appendix A.1, Table 3, printed p.32, PDF page index 31

The PDF text explicitly associates the two-unary/one-binary relational
sentence in PROOF.md Section 3 with A196460. The active-vertex/isolated-
vertex interpretation is an elementary reading of that sentence, which we
prove directly. The retrieved text had no match for `asympt` or `isolated`.
We do not infer from that alone an exhaustive absence of related results.
The PDF screenshot request failed, so the specific formula was verified
from extracted PDF text rather than a visual page inspection.

## Bounded overlap and literature search

Public search terms included:

* `"A196460" asymptotic`
* `"A196460" graph`
* `"A196460" -site:oeis.org -site:libris.ro`
* `"1, 5, 47, 1193" -site:oeis.org`
* `"A196460" "inverse"`
* `"A196460" "asymptotic expansion"`
* `"2^(n^2)" "Kotesovec" "2013" "196460"`
* Queries restricted to `github.com/VladimirReshetnikov/ProveIt`
  for `A196460`, `113855`, and `isolated vertices`

The exact-identifier literature search found the 2023 paper through the
OEIS citation index. It found no source giving the all-orders/inverse
theorems in this packet. This is a search result, not proof of novelty.

The following public ProveIt pages were retrieved and checked for the
sequence identifier:

* https://github.com/VladimirReshetnikov/ProveIt
* https://github.com/VladimirReshetnikov/ProveIt/tree/main/Combinatorics
* https://github.com/VladimirReshetnikov/ProveIt/blob/main/SetTheory/Cardinals/docs/reports/README.md

No A196460 match occurred in those retrieved pages. The report catalogue
also had no `bipartite` match. The incoming directory and raw catalogue
fetches failed. No repository-wide checkout, code search guarantee, or
remote commit pin is claimed. Cached web views need not cover every file.

The local search covered readable `.md`, `.tex`, and `.txt` files of at
most 2 MB under `/workspace/shared`, excluding the new packet. Its pattern
was `A196460|isolated vertices|isolated-vertex|clipping.table.*count`.
No matching path was returned. It did not search archives, binary files,
all code, or larger files. The permission-denied audit fixtures
are listed in `evidence/workspace-overlap-errors.txt`; no access escalation
or alternate route was attempted. The empty matching-path output is kept
alongside it. These limitations prevent an exhaustive-negative claim.

## Fresh execution and preservation

`verify_exact.py` was authored here, read in full before running, and run
using only Python standard-library integer and rational arithmetic. It
reads no project source or coefficient fixture. Its evidence file refuses
to overwrite an existing file. The first successful run is retained as
`evidence/exact.json` and `evidence/exact.log`.

The additional fresh standard-library `verify_connected.py`, also read
before running, reads only this packet's JSON evidence and checks the
leading coefficients of P_k, L_k, and D_k against the elementary
connected-component recurrence through order six. Its successful result
is in `evidence/connected.json` and `evidence/connected.log`.

`preserve_inputs.py` was also written here and read before running. It only
reads and hashes source bytes and metadata and writes a newly named JSON
inside this packet's evidence directory. It snapshots 249 entries across:

* both mathematical source directories and their two ZIP archives;
* the local Report 69 release tree;
* the local Report 70 release tree.

The before inventory was captured before the new algebra checker ran.
The broad equality check subsequently failed: concurrent release work
changed or added 132 entries, 44 in the Report 69 tree and 88 in the
Report 70 tree. The authentic 249-entry before inventory, 376-entry current
inventory, and 132-entry difference are retained in `evidence/input-before.json`,
`evidence/input-current.json`, and `evidence/input-changes.json`.
No whole-interval equality is claimed for those two active release trees.

All 62 core-source entries in the two mathematical source directories and
their archives remained exactly equal, including hashes, sizes, modes,
nanosecond mtimes, and directory metadata. A separate fresh comparison
certifies that narrower boundary. Access times are deliberately excluded,
since reading can update them. This is a fresh preservation interval, not
a retroactive claim about earlier work. Nothing in this task wrote to
either source packet or either concurrently active release tree.

At sealing, `seal_packet.py` repeats a fresh full 62-entry core-source
inventory and compares it to the original before inventory. It records
that final state in `evidence/core-final.json`, writes the payload hash
manifest, makes only the new packet read-only, and verifies every ZIP
member against its packet bytes. Its receipt is alongside the archive.

The new proof is an ordinary mathematical proof with exact-algebra
corroboration. None of it has been submitted to a theorem prover or to
OEIS, merged into a repository, or assigned a new report number.
