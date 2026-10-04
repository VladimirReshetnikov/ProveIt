# Review of the two bounded complete84 producer rewrites

**PASS with the stated restricted scope; no arithmetic saving.** The
joint-root schedule is an84-gate tie, and the first/main expansion costs87.
Both preserve the whole polynomial on the same supplied coordinates.

Reviewed SHA256 pins:

- `complete84_joint_root_cut.py`: `d110b0ef43e223af1748eabe80dbd3e53c3acb2a59c766e7e581e74dbd87ae87`
- `complete84_joint_root_cut.json`: `c8f8e2175f49f1b41aab0c91658da5e4dd8da1f9b7f2584abdf72fbba43e307f`
- `complete84_joint_root_cut.md`: `79cfda9e870ad63a848fb454266d1bca98f2117393edc57f99108b4c1cce780c`

I read the entire105-line helper and proof. The new helper authenticates
the current84 trio as inert bytes and checks exact sparse coefficients
of both roots before substituting common formal labels downstream.
Every other downstream expression is reconstructed from the full arrays;
all seven factor expressions and final output agree. Topological traversal
rejects cycles, unknown references, duplicate producers and dead rows.
Sharing rho*H requires a separate sigma*H and one extra root addition,
exactly offsetting the deleted gamma sum/product arrangement. Counting
all retained producer and consumer rows confirms47M+37A.

The independent-port bilinear flattening has rank4, which requires at
least4 separated bilinear multiplications: each contributes an outer
product of a left-input/output tensor with a right-input vector. With
at most6 core gates, at most2 additions remain. Combining four live
products into two outputs consumes at least2 postprocessing additions,
leaving no linear preprocessing. Raw-monomial products cannot then
produce the three-term first root and distinct two-term second root
with those two additions. More products cannot improve the gate total.
The two stipulated final offset additions raise the bound to9 gates.
The finite3600-case enumeration corroborates the raw ±1 subcase only;
the proof is correctly not based on that enumeration for arbitrary
scalar coefficients.

This argument treats a and H as independent. The actual identity H=4a+3,
nonlinear cancellation, changed producers and joint norm evaluation are
outside the bound. Neither the helper nor note extrapolates it to a
minimum for the actual84 polynomial.

The separate identity `(E+Y)*(kY+eta)=E*kY+E*eta+Y*(kY+eta)` is checked
coefficient by coefficient and against all four defining parent rows.
Replacing its single product adds1M+2A and changes no other rows; whole
source liveness gives48M+39A. The inherited polynomial identity proves
the same degree187 and positive zero relation without an inverse map.

Installed-path normal and optimized runs produce receipts identical to
the saved one. Eighty complete signed/rational assignments supplement
the exact identities. No predecessor code, old scout suite or historical
compiler was executed. This packet records two concrete unsuccessful
rewrites so future work can focus on larger cuts and actual producer
relations.
