# Growing-order sector continuation

This separate, self-contained proof extends the exact A196460 sector expansion
to every truncation order 0<=M<2n simultaneously. For n>=32 it computes the
exact worst relative tail excess and proves the optimal asymptotic constant
9/13. Merging the extra full clipping table only into the terminal sector
gives the clipping-table count C_n=a_n+1 a sharp bound 1/n, with equality at
M=2n-2. No source article or audit is changed.

- `PROOF.md`: complete analytic proof, coefficient-uniformity boundary, limits
- `SOURCES.md`: input identity and preservation scope
- `check_sectors.py`: fresh, source-free exact sector and tail checks
- `check_algebra.py`: fresh rational algebra and Gaussian-moment checks
- `preserve_inputs.py`: read-only source inventory comparison
- `seal_packet.py`: manifest, read-only delivery modes, ZIP and receipt
- `evidence/`: completed results, logs and before/after input inventories

For a source-free arithmetic replay, copy the two `check_*.py` files to a fresh
directory, create an `evidence` subdirectory there, and run each with Python
3.10 or later. Both refuse to overwrite their JSON output. The preservation
script intentionally refers to the two named local source directories; it is
not a source-free portability interface. No source or upstream program is
run or imported by any checker.

The theorem's threshold 32 is an elementary analytic threshold, not a claim of
minimality. The evidence records small-index behavior separately. The inverse
expansion remains fixed-order; no uniform growing-order inverse theorem is
claimed. There is no novelty claim, repository publication or external upload.

The manifest covers every payload file. The adjacent ZIP also includes the
manifest, and the adjacent receipt pins their hashes and archive verification.
Read-only modes are a delivery convention, not WORM storage, an external
timestamp, or a claim that later alteration is impossible.
