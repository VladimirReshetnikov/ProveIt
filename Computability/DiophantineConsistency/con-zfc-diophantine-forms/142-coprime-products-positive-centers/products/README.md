# Selective coprime products for Con(ZFC)

Three complete ordinary polynomials, all with strictly positive integer
unknowns and the exact indexed943/radix67 coefficient tuple:

| File | Unknowns | Live binary operations | Exact degree |
|---|---:|---:|---:|
| equation_14_raw.json | 14 | 70 | 189 |
| equation_14_reduced.json | 14 | 71 | 157 |
| equation_13_anchored.json | 13 | 72 | 433 |

Each file's ordered `source` list is a straight-line polynomial definition.
Only the listed `witnesses` are variables; `fixed_numerals` are the four
specified constant leaves, and every other name denotes an abbreviation.
The equation is the value of the listed `output` equal to zero.

`PROOF.md` proves the two fourteen-variable constructions.
`ROOT_ANCHOR_PROOF.md` proves the thirteen-variable composition.
The proofs use the inherited exact P66 native/refutation calibration,
retained in `parents/P66_PROOF.md`; the enclosing report identifies its
source closure and ordinary, rather than newly kernel-certified, status.
The four complete fixed integer payloads and original binding are included.
They use unsigned little-endian integer bytes after gzip decompression;
MF is already shifted and must not be shifted again.

Run with Python 3.10 or later; the standard library suffices:

    python3 build.py --check
    python3 verify.py
    python3 -O verify.py

The first command reconstructs the three full graphs in memory and compares
their serialization with the delivered files. Without `--check`, build.py
rewrites only those three generated graph files. The verifier is read-only.
Its saved normal and optimized receipts are byte-identical. It authenticates
all fixed coefficient bytes, checks literal parent-prefix preservation,
topology, liveness, operation counts, exact degree certificates, independent
full-formula evaluations, root-extraction arithmetic, and finite Pell
period examples. It also checks a concrete failed extraction after removing
the coprimality hypothesis, and rejects an arithmetic mutation.

The graph tests are not a substitute for the unbounded mathematical proofs.
No consistency decision, global optimum, literature-wide priority, or new
end-to-end formal-kernel certificate is asserted. Coprime product squares
and cofinal Pell divisibility have explicit predecessors in the repository; the
contribution is the selective construction and these measured endpoints.
