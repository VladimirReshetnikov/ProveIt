# Ten positive variables, exact degree 190

The literal ordinary Diophantine equation in `equation.json` has ten strictly
positive integer variables, exact degree190, and120 live binary arithmetic
operations (75 multiplications,24 additions,21 subtractions).

The new ingredient is a transport weight `L=b^2 U E`. It lets the whole-product
polynomial center of ProveIt package178 operate in package172's lower-degree
free chart even when the auxiliary Pell index is three. The signed inequality
is proved before the sign of the encoded transport quotient is known. All
four fixed numerical coefficients remain exactly the calibrated parent tuple.

`PROOF.md` gives the entire formula, the new unbounded proof, exact leading
form, inherited calibration boundary, comparison, and further research.
An ordinary mathematical proof, composed with the named inherited native and
syntactic calibration, establishes in ZFC that this equation has no positive
integer zero if and only if Con(ZFC). This is not a proof of consistency or
unsolvability and is not a newly compiled formal-kernel proof.

| Matched equation | Positive variables | Binary operations | Exact degree |
|---|---:|---:|---:|
| Incoming centered free chart |10|90|206|
| Source178 scaled whole-product center |10|116|208|
| This weighted free-chart center |10|120|190|

This is a degree/operation tradeoff. It does not assert a global minimum or
literature-wide priority. The new bound, rather than a silent transfer of the
scaled chart's stronger index exclusion, is what licenses the composition.

## Reproduce

Python3.10 or newer and its standard library suffice:

    python3 -B build.py --check
    python3 -B verify.py
    python3 -B -O verify.py
    python3 -B rebuild_coefficients.py

The independent verifier imports neither the producer nor an inherited
checker. It checks all actual graph gates, domain and liveness,84 center
monomials,594 norm-defect monomials, the exact weighted degree94 defect,
the complete198-term degree190 form, all four numerical payload hashes, and
60 deliberately corrupted center operators. The coefficient reconstruction
recovers the entire unchanged tuple from its frozen436-character finite seed.
These are finite artifact checks and do not substitute for unbounded proofs.

`inherited/` contains the immediate free-chart proof and exact parent graph,
the center proof and algebra, and the finite numeral recipe. It is a selected
proof interface, not a full compilable Lean/Rocq dependency closure. Original
descriptions in copied historical documents belong to those source documents;
their numerical and proof scopes are not newly asserted for this package.

The four `.bin.gz` files are little-endian unsigned integer payloads after
decompression. The largest fixed integer has592,884 bits. Fixed integer leaves
are free in the displayed arithmetic-operation count; that count is not a
bit-complexity measure.

The construction is based on a fixed repository snapshot and two explicitly
identified predecessors. `SOURCES.json` records their paths and hashes.
